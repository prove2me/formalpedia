-- Prove2me | solution 1 for OAI.HyperbolicCoding.actual_fixed_window_rate_copy_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:14:39.142418+00:00
-- url     : https://prove2.me/submissions/2c0ffc8c-04eb-4731-ae3d-018dcc205760

import Mathlib
import Definitions.Def_OAIQ44C000
import Definitions.Def_OAIQ44C001

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
lemma obs_factor (p : Ω → α) (g : α → β) (hp : Measurable p) (hg : Measurable (g ∘ p)) :
    obs μ (g ∘ p) ≤ obs μ p := by
  have h := obs_pair_ge_right μ p (g ∘ p) hp hg
  simpa only [Function.comp_def,obs_pair_function] using h

lemma sum_mass_mul_integral (p : Ω → α) (hp : Measurable p) (g : α → ℝ) :
    ∑ a,mass μ p a*g a=∫ x,g (p x) ∂μ := by
  classical
  have he (x : Ω) : (∑ a : α,(p ⁻¹' {a}).indicator (fun _ => g a) x)=g (p x) := by
    simp only [indicator_apply,mem_preimage,mem_singleton_iff,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [←show (fun x => ∑ a : α,(p ⁻¹' {a}).indicator (fun _ => g a) x)=(fun x => g (p x)) from funext he]
  rw [integral_finsetSum _ (fun a _ => (integrable_const _).indicator (hp (measurableSet_singleton a)))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_indicator (hp (measurableSet_singleton a)),integral_const,Measure.real,Measure.restrict_apply_univ]
  rfl

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
lemma obs_word_comparison (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) (n : ℕ) :
    obs μ (word f p n) ≤ obs μ (word f q n)+n*cond μ p q := by
  have h := obs_pair_ge_left μ (word f p n) (word f q n)
    (word_measurable f hf.measurable p hp n) (word_measurable f hf.measurable q hq n)
  have hc := cond_word_bound μ f hf p q hp hq n
  unfold cond at hc ⊢
  linarith

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
lemma rate_comparison (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) : rate μ f p ≤ rate μ f q+cond μ p q := by
  apply le_of_tendsto_of_tendsto (rate_tendsto μ f hf p hp) ((rate_tendsto μ f hf q hq).add_const _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  have h := div_le_div_of_nonneg_right (obs_word_comparison μ f hf p q hp hq n) hn0.le
  simpa only [add_div,mul_div_cancel_left₀ _ hn0.ne'] using h

end StandardMapEntropy.Entropy

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
variable {X : Type*} [MeasurableSpace X]

lemma integerIterate_add (e : X ≃ᵐ X) (m n : ℤ) (x : X) :
    integerIterate e (m+n) x=integerIterate e m (integerIterate e n x) := by
  simp only [integerIterate,zpow_add,Equiv.Perm.coe_mul,Function.comp_apply]
lemma integerIterate_nat (e : X ≃ᵐ X) (n : ℕ) (x : X) : integerIterate e n x=e^[n] x := by
  simp only [integerIterate,zpow_natCast,Equiv.Perm.coe_pow,MeasurableEquiv.coe_toEquiv]
lemma integerIterate_neg_nat (e : X ≃ᵐ X) (n : ℕ) (x : X) : integerIterate e (-(n : ℤ)) x=e.symm^[n] x := by
  simp only [integerIterate,zpow_neg,zpow_natCast,←inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow]
  rfl
lemma integerIterate_nat_fun (e : X ≃ᵐ X) (n : ℕ) : integerIterate e (n : ℤ)=e^[n] :=
  funext (integerIterate_nat e n)
lemma integerIterate_neg_nat_fun (e : X ≃ᵐ X) (n : ℕ) : integerIterate e (-(n : ℤ))=e.symm^[n] :=
  funext (integerIterate_neg_nat e n)
lemma integerIterate_measurable (e : X ≃ᵐ X) (n : ℤ) : Measurable (integerIterate e n) := by
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_natCast,integerIterate_nat_fun] using e.measurable.iterate m
  | negSucc m =>
    have hn : Int.negSucc m= -((m+1 : ℕ) : ℤ) := by omega
    simpa only [hn,integerIterate_neg_nat_fun] using e.symm.measurable.iterate (m+1)
lemma integerIterate_measurePreserving (e : X ≃ᵐ X) {μ : Measure X}
    (he : MeasurePreserving e μ μ) (n : ℤ) : MeasurePreserving (integerIterate e n) μ μ := by
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_natCast,integerIterate_nat_fun] using he.iterate m
  | negSucc m =>
    have hn : Int.negSucc m= -((m+1 : ℕ) : ℤ) := by omega
    simpa only [hn,integerIterate_neg_nat_fun] using (he.symm e).iterate (m+1)

end HyperbolicCoding

end
section
open MeasureTheory Set Filter

namespace HyperbolicCoding
variable {X A : Type*} [MeasurableSpace X]

lemma iterateEquiv_apply (e : X ≃ᵐ X) (n : ℕ) (x : X) : iterateEquiv e n x=e^[n] x := by
  change ((e.toEquiv^n) x)=_
  rw [Equiv.Perm.coe_pow]
  rfl
lemma iterateEquiv_measurePreserving (e : X ≃ᵐ X) {μ : Measure X}
    (he : MeasurePreserving e μ μ) (n : ℕ) : MeasurePreserving (iterateEquiv e n) μ μ := by
  have hh : (iterateEquiv e n : X → X)=e^[n] := funext (iterateEquiv_apply e n)
  rw [hh]
  exact he.iterate n

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma LawClose.symm {μ ν : Measure X} {ε : ℝ} (h : LawClose μ ν ε) : LawClose ν μ ε := by
  intro D hD
  rw [abs_sub_comm]
  exact h D hD

lemma LawClose.triangle {μ ν κ : Measure X} {ε δ : ℝ}
    (h : LawClose μ ν ε) (h' : LawClose ν κ δ) : LawClose μ κ (ε+δ) := by
  intro D hD
  exact (abs_sub_le (μ.real D) (ν.real D) (κ.real D)).trans (add_le_add (h D hD) (h' D hD))

lemma LawClose.map {μ ν : Measure X} {ε : ℝ} (h : LawClose μ ν ε)
    {f : X → Y} (hf : Measurable f) : LawClose (μ.map f) (ν.map f) ε := by
  intro D hD
  simp only [Measure.real,Measure.map_apply hf hD]
  exact h _ (hD.preimage hf)

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

lemma LawClose.mono {μ ν : Measure X} {ε δ : ℝ} (h : LawClose μ ν ε) (hεδ : ε≤δ) :
    LawClose μ ν δ := fun D hD => (h D hD).trans hεδ

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
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_FiniteMaximalCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem finite_maximal_coupling_equal_mass {A : Type*} [Fintype A] [DecidableEq A]
    (p q : A → ℝ) (hp : ∀ a,0≤p a) (hq : ∀ a,0≤q a)
    (heq : ∑ a,p a=∑ a,q a) :
    ∃ r : A → A → ℝ,(∀ a b,0 ≤ r a b) ∧
      (∀ a,∑ b,r a b=p a) ∧ (∀ b,∑ a,r a b=q b) ∧
      (∑ a,∑ b,r a b*(if a=b then 0 else 1))=∑ a,max (p a-q a) 0 := by
  classical
  let d : A → ℝ := fun a => min (p a) (q a)
  let u : A → ℝ := fun a => p a-d a
  let v : A → ℝ := fun a => q a-d a
  let t : ℝ := ∑ a,u a
  have hd (a) : 0≤d a := le_min (hp a) (hq a)
  have hu (a) : 0≤u a := sub_nonneg.mpr (min_le_left _ _)
  have hv (a) : 0≤v a := sub_nonneg.mpr (min_le_right _ _)
  have ht : 0≤t := Finset.sum_nonneg (fun a _ => hu a)
  have htv : ∑ a,v a=t := by
    dsimp only [t,u,v]
    rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,heq]
  have huv (a) : u a*v a=0 := by
    rcases le_total (p a) (q a) with ha | ha
    · simp only [u,v,d,min_eq_left ha,sub_self,zero_mul]
    · simp only [u,v,d,min_eq_right ha,sub_self,mul_zero]
  have hmax (a) : u a=max (p a-q a) 0 := by
    rcases le_total (p a) (q a) with ha | ha
    · simp only [u,d,min_eq_left ha,sub_self,max_eq_right (sub_nonpos.mpr ha)]
    · simp only [u,d,min_eq_right ha,max_eq_left (sub_nonneg.mpr ha)]
  by_cases ht0 : t=0
  · have hu0 (a) : u a=0 := by
      have hh := Finset.single_le_sum (fun b _ => hu b) (Finset.mem_univ a)
      change u a≤t at hh
      rw [ht0] at hh
      exact le_antisymm hh (hu a)
    have hv0 (a) : v a=0 := by
      have hh := Finset.single_le_sum (fun b _ => hv b) (Finset.mem_univ a)
      rw [htv,ht0] at hh
      exact le_antisymm hh (hv a)
    refine ⟨fun a b => if a=b then p a else 0,?_,?_,?_,?_⟩
    · intro a b
      dsimp only
      split_ifs
      · exact hp a
      · exact le_rfl
    · intro a; simp
    · intro b
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      have h1 := hu0 b
      have h2 := hv0 b
      dsimp [u,v] at h1 h2
      linarith
    · have he (a b : A) : (if a=b then p a else 0)*(if a=b then (0 : ℝ) else 1)=0 := by
        by_cases h : a=b <;> simp [h]
      simp_rw [he]
      simp only [Finset.sum_const_zero]
      rw [←show (∑ a,u a)=(∑ a,max (p a-q a) 0) from Finset.sum_congr rfl (fun a _ => hmax a)]
      exact ht0.symm
  · have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
    let r : A → A → ℝ := fun a b => (if a=b then d a else 0)+u a*v b/t
    have hr (a b) : 0 ≤ r a b := by
      dsimp only [r]
      exact add_nonneg (by split_ifs; exact hd a; exact le_rfl) (div_nonneg (mul_nonneg (hu a) (hv b)) ht)
    have hrow (a) : ∑ b,r a b=p a := by
      simp only [r,Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
        ←Finset.sum_div,←Finset.mul_sum,htv,mul_div_cancel_right₀ _ ht0]
      dsimp only [u]
      ring
    have hcol (b) : ∑ a,r a b=q b := by
      simp only [r,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
        ←Finset.sum_div,←Finset.sum_mul]
      change d b+t*v b/t=q b
      rw [mul_div_cancel_left₀ _ ht0]
      dsimp only [v]
      ring
    refine ⟨r,hr,hrow,hcol,?_⟩
    have hoff (a b) : r a b*(if a=b then 0 else 1)=u a*v b/t := by
      by_cases hab : a=b
      · subst b; simp [huv]
      · simp only [r,ite_eq_right hab,zero_add,mul_one]
    simp_rw [hoff]
    simp only [←Finset.sum_div,←Finset.mul_sum,htv,mul_div_cancel_right₀ _ ht0]
    exact Finset.sum_congr rfl (fun a _ => hmax a)

theorem finite_maximal_coupling {A : Type*} [Fintype A] [DecidableEq A]
    (p q : A → ℝ) (hp : ∀ a,0≤p a) (hq : ∀ a,0≤q a)
    (hp1 : ∑ a,p a=1) (hq1 : ∑ a,q a=1) :
    ∃ r : A → A → ℝ,(∀ a b,0 ≤ r a b) ∧
      (∀ a,∑ b,r a b=p a) ∧ (∀ b,∑ a,r a b=q b) ∧
      (∑ a,∑ b,r a b*(if a=b then 0 else 1))=∑ a,max (p a-q a) 0 :=
  finite_maximal_coupling_equal_mass p q hp hq (hp1.trans hq1.symm)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped BigOperators ENNReal

lemma positive_mass_difference_le {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (h : LawClose μ ν ε) :
    (∑ a,max (μ.real {a}-ν.real {a}) 0)≤ε := by
  classical
  let D := Finset.univ.filter (fun a : A => ν.real {a}≤μ.real {a})
  have hm (a : A) : max (μ.real {a}-ν.real {a}) 0=
      if ν.real {a}≤μ.real {a} then μ.real {a}-ν.real {a} else 0 := by
    split_ifs with ha
    · exact max_eq_left (sub_nonneg.mpr ha)
    · exact max_eq_right (sub_nonpos.mpr (le_of_not_ge ha))
  have he : (∑ a,max (μ.real {a}-ν.real {a}) 0)=μ.real D-ν.real D := by
    simp_rw [hm]
    rw [←Finset.sum_filter]
    change (∑ a∈D,(μ.real {a}-ν.real {a}))=_
    rw [Finset.sum_sub_distrib,sum_measureReal_singleton,sum_measureReal_singleton]
  rw [he]
  exact (le_abs_self _).trans (h D D.measurableSet)

theorem finite_coupling_of_lawClose {A : Type*} [Fintype A] [DecidableEq A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (h : LawClose μ ν ε) :
    ∃ r : A → A → ℝ,(∀ a b,0 ≤ r a b) ∧
      (∀ a,∑ b,r a b=μ.real {a}) ∧ (∀ b,∑ a,r a b=ν.real {b}) ∧
      (∑ a,∑ b,r a b*(if a=b then 0 else 1))≤ε := by
  obtain ⟨r,hr,hrow,hcol,herr⟩ := finite_maximal_coupling (fun a => μ.real {a}) (fun a => ν.real {a})
    (fun _ => measureReal_nonneg) (fun _ => measureReal_nonneg)
    (by simp)
    (by simp)
  exact ⟨r,hr,hrow,hcol,herr.le.trans (positive_mass_difference_le μ ν h)⟩

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ} {s : C → ℝ}

lemma left_nonneg (r : MatrixCoupling p q) (a : A) : 0≤p a := by
  rw [←r.row a]
  exact Finset.sum_nonneg (fun b _ => r.nonneg a b)

lemma comp_cost_le (r : MatrixCoupling p q) (t : MatrixCoupling q s)
    (d : A → B → ℝ) (e : B → C → ℝ) (f : A → C → ℝ)
    (htri : ∀ a b c,f a c≤d a b+e b c) :
    (r.comp t).cost f ≤ r.cost d+t.cost e := by
  unfold cost comp
  simp only [Finset.sum_mul]
  calc
    _≤∑ a,∑ c,∑ b,glueWeight r t a b c*(d a b+e b c) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun c _ =>
        Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (htri a b c) (glueWeight_nonneg r t a b c))))
    _=(∑ a,∑ c,∑ b,glueWeight r t a b c*d a b)+
        (∑ a,∑ c,∑ b,glueWeight r t a b c*e b c) := by
      simp only [mul_add,Finset.sum_add_distrib]
    _=(∑ a,∑ b,r.weight a b*d a b)+(∑ b,∑ c,t.weight b c*e b c) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
        simp only [←Finset.sum_mul,glueWeight_row]
      · rw [Finset.sum_comm]
        calc
          _ = ∑ c,∑ b,∑ a,glueWeight r t a b c*e b c := by
            apply Finset.sum_congr rfl
            intro c _
            exact Finset.sum_comm
          _ = ∑ c,∑ b,t.weight b c*e b c := by simp only [←Finset.sum_mul,glueWeight_col]
          _ = _ := Finset.sum_comm

end MatrixCoupling
end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]

lemma integrable_finite_observation (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → A) (hp : Measurable p) (g : A → ℝ) : Integrable (fun x => g (p x)) μ := by
  classical
  apply Integrable.of_bound ((measurable_of_countable g).comp hp).aestronglyMeasurable (∑ a,|g a|)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun a _ => abs_nonneg (g a)) (Finset.mem_univ _))

lemma information_measurable (μ : Measure X) (p : X → A) (hp : Measurable p) :
    Measurable (information μ p) := (measurable_of_countable (fun a : A => -Real.log (mass μ p a))).comp hp

lemma information_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → A) (hp : Measurable p) : Integrable (information μ p) μ :=
  integrable_finite_observation μ p hp (fun a : A => -Real.log (mass μ p a))

lemma integral_information (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → A) (hp : Measurable p) : (∫ x,information μ p x ∂μ)=obs μ p := by
  simp only [information]
  rw [←sum_mass_mul_integral μ p hp (fun a => -Real.log (mass μ p a))]
  simp only [obs,shannon,Real.negMulLog,mul_neg,neg_mul]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma ae_mass_positive (μ : Measure X) [IsFiniteMeasure μ] (p : X → A) :
    ∀ᵐ x ∂μ,0 < mass μ p (p x) := by
  have hzero (a : A) : ∀ᵐ x ∂μ,mass μ p a=0 → p x≠a := by
    by_cases ha : mass μ p a=0
    · have hm : μ (p ⁻¹' {a})=0 := by
        apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) ENNReal.zero_ne_top).mp
        exact ha
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hm] with x hx _h
      exact hx
    · exact ae_of_all _ (fun _ h => (ha h).elim)
  filter_upwards [ae_all_iff.mpr hzero] with x hx
  exact lt_of_le_of_ne (mass_nonneg μ p _) (Ne.symm (fun h => hx (p x) h rfl))

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped ENNReal Topology

lemma continuous_cdf_atomless (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : Continuous (cdf ν) := by
  have hc : Continuous (fun a : ℝ => ∫ _x in Iic a,(1 : ℝ) ∂ν) := by
    rw [continuous_iff_continuousAt]
    intro a
    have h := ((integrable_const (1 : ℝ)).integrableOn : IntegrableOn (fun _x : ℝ => (1 : ℝ)) (Iic (a+1)) ν)
    exact (h.continuousOn_Iic_primitive_Iic a (by simp)).continuousAt (Iic_mem_nhds (by linarith))
  simpa only [integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ,←cdf_eq_real] using hc

theorem exists_event_real_mass {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
    ∃ E : Set X,MeasurableSet E ∧ μ.real E=t := by
  by_cases ht0 : t=0
  · exact ⟨∅,MeasurableSet.empty,by simp [ht0]⟩
  by_cases hte : t=1
  · exact ⟨univ,MeasurableSet.univ,by simp [hte]⟩
  let b : X → ℝ := embeddingReal X
  have hb : MeasurableEmbedding b := measurableEmbedding_embeddingReal X
  let ν := μ.map b
  have : IsProbabilityMeasure ν := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : NullSingletonClass ν := by
    constructor
    intro y
    rw [show ν=μ.map b from rfl,Measure.map_apply hb.measurable (measurableSet_singleton y)]
    by_cases hy : ∃ x,b x=y
    · obtain ⟨x,rfl⟩ := hy
      have hs : b ⁻¹' {b x}={x} := by
        ext z
        exact hb.injective.eq_iff
      simp only [hs,measure_singleton]
    · have hs : b ⁻¹' {y}=∅ := eq_empty_iff_forall_notMem.mpr (fun x hx => hy ⟨x,hx⟩)
      simp only [hs,measure_empty]
  have hs := isPreconnected_univ.intermediate_value_Ioo (s:=Set.univ)
    (show (atBot : Filter ℝ)≤𝓟 Set.univ by simp) (show (atTop : Filter ℝ)≤𝓟 Set.univ by simp)
    (continuous_cdf_atomless ν).continuousOn (tendsto_cdf_atBot ν) (tendsto_cdf_atTop ν)
    (show t∈Ioo (0 : ℝ) 1 from ⟨lt_of_le_of_ne ht (Ne.symm ht0),lt_of_le_of_ne ht1 hte⟩)
  obtain ⟨r,_hr,hrt⟩ := hs
  refine ⟨b ⁻¹' Iic r,measurableSet_Iic.preimage hb.measurable,?_⟩
  rw [←map_measureReal_apply hb.measurable measurableSet_Iic]
  exact (cdf_eq_real ν r).symm.trans hrt

theorem exists_subset_real_mass {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {S : Set X} (hS : MeasurableSet S) {t : ℝ} (ht : 0≤t) (htS : t≤μ.real S) :
    ∃ E : Set X,MeasurableSet E ∧ E⊆S ∧ μ.real E=t := by
  by_cases ht0 : t=0
  · exact ⟨∅,MeasurableSet.empty,empty_subset _,by simp [ht0]⟩
  have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hSr : 0<μ.real S := htpos.trans_le htS
  have hS0 : μ S≠0 := by
    intro h
    simp only [Measure.real,h,ENNReal.toReal_zero] at hSr
    exact lt_irrefl _ hSr
  let ν : Measure X := (μ S)⁻¹ • μ.restrict S
  have : IsProbabilityMeasure ν := by
    constructor
    simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply MeasurableSet.univ,univ_inter]
    exact ENNReal.inv_mul_cancel hS0 (measure_ne_top μ S)
  have : NullSingletonClass ν := by
    constructor
    intro x
    have hz : μ ({x}∩S)=0 := measure_mono_null inter_subset_left (measure_singleton x)
    simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply (measurableSet_singleton x),hz,mul_zero]
  obtain ⟨T,hT,hTm⟩ := exists_event_real_mass ν (div_nonneg ht hSr.le) ((div_le_one hSr).mpr htS)
  refine ⟨S∩T,hS.inter hT,inter_subset_left,?_⟩
  have he : ν.real T=μ.real (S∩T)/μ.real S := by
    simp only [ν,Measure.real,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hT,
      ENNReal.toReal_mul,ENNReal.toReal_inv,inter_comm T S,div_eq_mul_inv]
    ring
  rw [he] at hTm
  exact (div_left_inj' hSr.ne').mp hTm

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_AtomlessFinitePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]

theorem exists_disjoint_cuts (s : Finset A) (w : A → ℝ) (hw : ∀ a,0≤w a)
    {S : Set X} (hS : MeasurableSet S) (hsum : (∑ a∈s,w a)≤μ.real S) :
    ∃ E : A → Set X,(∀ a∈s,MeasurableSet (E a) ∧ E a⊆S ∧ μ.real (E a)=w a) ∧
      (∀ a∈s,∀ b∈s,a≠b → Disjoint (E a) (E b)) := by
  classical
  induction s using Finset.induction_on generalizing S with
  | empty => exact ⟨fun _ => ∅,by simp,by simp⟩
  | @insert a s ha ih =>
    have hsumnonneg : 0≤∑ b∈s,w b := Finset.sum_nonneg (fun b _ => hw b)
    rw [Finset.sum_insert ha] at hsum
    obtain ⟨D,hD,hDS,hDm⟩ := exists_subset_real_mass μ hS (hw a) (by linarith)
    have hrem : (∑ b∈s,w b)≤μ.real (S\D) := by
      rw [measureReal_sdiff hDS hD,hDm]
      linarith
    obtain ⟨F,hF,hFd⟩ := ih (hS.diff hD) hrem
    refine ⟨fun b => if b=a then D else F b,?_,?_⟩
    · intro b hb
      by_cases hba : b=a
      · subst b
        simpa using And.intro hD (And.intro hDS hDm)
      · have hbs : b∈s := (Finset.mem_insert.mp hb).resolve_left hba
        simpa only [ite_eq_right hba] using And.intro (hF b hbs).1
          (And.intro ((hF b hbs).2.1.trans sdiff_subset) (hF b hbs).2.2)
    · intro b hb c hc hbc
      by_cases hba : b=a
      · subst b
        have hca : c≠a := Ne.symm hbc
        have hcs := (Finset.mem_insert.mp hc).resolve_left hca
        simp only [ite_eq_right hca]
        exact disjoint_left.mpr (fun x hxD hxF => ((hF c hcs).2.1 hxF).2 hxD)
      · by_cases hca : c=a
        · subst c
          have hbs := (Finset.mem_insert.mp hb).resolve_left hba
          simp only [ite_eq_right hba]
          exact disjoint_left.mpr (fun x hxF hxD => ((hF b hbs).2.1 hxF).2 hxD)
        · simp only [ite_eq_right hba,ite_eq_right hca]
          exact hFd b ((Finset.mem_insert.mp hb).resolve_left hba) c
            ((Finset.mem_insert.mp hc).resolve_left hca) hbc

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set

lemma exists_measurable_coloring {X A : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Nonempty A] (s : Finset A) (E : A → Set X)
    (hm : ∀ a∈s,MeasurableSet (E a))
    (hd : ∀ a∈s,∀ b∈s,a≠b → Disjoint (E a) (E b)) :
    ∃ q : X → A,Measurable q ∧ ∀ a∈s,∀ x∈E a,q x=a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.arbitrary A,measurable_const,by simp⟩
  | @insert a s ha ih =>
    obtain ⟨q,hq,hqa⟩ := ih (fun b hb => hm b (Finset.mem_insert_of_mem hb))
      (fun b hb c hc => hd b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc))
    let q' : X → A := (E a).piecewise (fun _ => a) q
    refine ⟨q',measurable_const.piecewise (hm a (Finset.mem_insert_self _ _)) hq,?_⟩
    intro b hb x hx
    by_cases hba : b=a
    · subst b
      exact Set.piecewise_eq_of_mem _ _ _ hx
    · have hbs := (Finset.mem_insert.mp hb).resolve_left hba
      have hxa : x∉E a := fun hxa => (hd b hb a (Finset.mem_insert_self _ _) hba).le_bot ⟨hx,hxa⟩
      exact (Set.piecewise_eq_of_notMem _ _ _ hxa).trans (hqa b hbs x hx)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators

theorem exists_finite_random_variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [Nonempty A]
    (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {S : Set X} (hS : MeasurableSet S) (w : A → ℝ) (hw : ∀ a,0≤w a)
    (hwS : ∑ a,w a=μ.real S) :
    ∃ q : X → A,Measurable q ∧ ∀ a,μ.real (S∩q ⁻¹' {a})=w a := by
  classical
  obtain ⟨E,hE,hEd⟩ := exists_disjoint_cuts μ Finset.univ w hw hS hwS.le
  have hm (a : A) := (hE a (Finset.mem_univ a)).1
  have hsub (a : A) := (hE a (Finset.mem_univ a)).2.1
  have he (a : A) := (hE a (Finset.mem_univ a)).2.2
  have hd : Pairwise (Function.onFun Disjoint E) := fun a b hab =>
    hEd a (Finset.mem_univ a) b (Finset.mem_univ b) hab
  obtain ⟨q,hq,hqa⟩ := exists_measurable_coloring Finset.univ E
    (fun a _ => hm a) (fun a _ b _ => hd (i:=a) (j:=b))
  have hUm : MeasurableSet (⋃ a,E a) := MeasurableSet.iUnion hm
  have hUS : (⋃ a,E a)⊆S := iUnion_subset hsub
  have hUr : μ.real (⋃ a,E a)=μ.real S := by
    rw [measureReal_iUnion_fintype hd hm]
    simp_rw [he]
    exact hwS
  have hz : μ (S\⋃ a,E a)=0 := (measureReal_eq_zero_iff).mp (by
    rw [measureReal_sdiff hUS hUm,hUr,sub_self])
  have hAE : ∀ᵐ x ∂μ,x∈S → ∃ a,x∈E a := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx hxS
    by_contra hh
    apply hx
    exact ⟨hxS,by simpa only [mem_iUnion,not_exists] using hh⟩
  refine ⟨q,hq,fun a => ?_⟩
  have hEq : (S∩q ⁻¹' {a} : Set X) =ᵐ[μ] E a := by
    filter_upwards [hAE] with x hx
    apply propext
    constructor
    · rintro ⟨hxS,hxq⟩
      obtain ⟨b,hxb⟩ := hx hxS
      have hba : b=a := (hqa b (Finset.mem_univ b) x hxb).symm.trans hxq
      change x∈E a
      exact hba ▸ hxb
    · intro hxa
      exact ⟨hsub a hxa,hqa a (Finset.mem_univ a) x hxa⟩
  exact (measureReal_congr hEq).trans (he a)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B C D : Type*} [MeasurableSpace X]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]

lemma symbolCost_self {E : Type*} (a : E) : symbolCost a a=0 := by simp [symbolCost]
lemma symbolCost_nonneg {E : Type*} (a b : E) : 0≤ symbolCost a b := by unfold symbolCost; split <;> norm_num
lemma symbolCost_triangle {E : Type*} (a b c : E) : symbolCost a c≤ symbolCost a b+symbolCost b c := by
  classical
  by_cases h1 : a=b <;> by_cases h2 : b=c <;> by_cases h3 : a=c <;> simp_all [symbolCost]

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_SequentialChunkCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

lemma productWeights_sum (w : B → A → ℝ) (hw : ∀ b,∑ a,w b a=1) :
    ∑ D,productWeights w D=1 := by
  unfold productWeights
  rw [←Fintype.prod_sum]
  simp only [hw,Finset.prod_const_one]

omit [Fintype A] [DecidableEq B] in
lemma productWeights_nonneg (w : B → A → ℝ) (hw : ∀ b a,0≤w b a) (D : B → A) :
    0≤productWeights w D := Finset.prod_nonneg (fun b _ => hw b (D b))

lemma expectation_product (w f : B → A → ℝ) :
    finiteExpectation (productWeights w) (fun D => ∏ b,f b (D b))=
      ∏ b,∑ a,w b a*f b a := by
  simp only [finiteExpectation,productWeights,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun b a => w b a*f b a)).symm

omit [Fintype A] in
lemma product_one_coordinate (b : B) (f : A → ℝ) (D : B → A) :
    (∏ i,if i=b then f (D i) else 1)=f (D b) := by
  simp

lemma expectation_coordinate (w : B → A → ℝ) (hw : ∀ b,∑ a,w b a=1)
    (b : B) (f : A → ℝ) :
    finiteExpectation (productWeights w) (fun D => f (D b))=∑ a,w b a*f a := by
  have h := expectation_product w (fun i a => if i=b then f a else 1)
  simp only [product_one_coordinate] at h
  rw [h]
  have hh (i : B) : (∑ a,w i a*(if i=b then f a else 1))=
      if i=b then ∑ a,w b a*f a else 1 := by
    by_cases hi : i=b
    · subst i; simp
    · simp [hi,hw]
  simp_rw [hh]
  simp

lemma expectation_distinct_coordinates (w : B → A → ℝ) (hw : ∀ b,∑ a,w b a=1)
    (b c : B) (hbc : b≠c) (f g : A → ℝ) :
    finiteExpectation (productWeights w) (fun D => f (D b)*g (D c))=
      (∑ a,w b a*f a)*(∑ a,w c a*g a) := by
  have h := expectation_product w
    (fun i a => (if i=b then f a else 1)*(if i=c then g a else 1))
  simp only [Finset.prod_mul_distrib,product_one_coordinate] at h
  rw [h]
  have hh (i : B) : (∑ a,w i a*((if i=b then f a else 1)*(if i=c then g a else 1)))=
      (if i=b then ∑ a,w b a*f a else 1)*(if i=c then ∑ a,w c a*g a else 1) := by
    by_cases hb : i=b
    · subst i; simp [hbc]
    · by_cases hc : i=c
      · subst i; simp [Ne.symm hbc]
      · simp [hb,hc,hw]
  simp_rw [hh]
  rw [Finset.prod_mul_distrib]
  simp

section Linear
variable {E I : Type*} [Fintype E] [Fintype I] (v : E → ℝ)
lemma finiteExpectation_add (F G : E → ℝ) :
    finiteExpectation v (fun x => F x+G x)=finiteExpectation v F+finiteExpectation v G := by
  simp [finiteExpectation,mul_add,Finset.sum_add_distrib]
lemma finiteExpectation_const (c : ℝ) : finiteExpectation v (fun _ => c)=(∑ x,v x)*c := by
  simp [finiteExpectation,Finset.sum_mul]
lemma finiteExpectation_smul (c : ℝ) (F : E → ℝ) :
    finiteExpectation v (fun x => c*F x)=c*finiteExpectation v F := by
  simp only [finiteExpectation,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring
lemma finiteExpectation_sum (F : I → E → ℝ) :
    finiteExpectation v (fun x => ∑ i,F i x)=∑ i,finiteExpectation v (F i) := by
  simp only [finiteExpectation,Finset.mul_sum]
  exact Finset.sum_comm
lemma finiteExpectation_mono (hv : ∀ x,0≤v x) (F G : E → ℝ) (h : ∀ x,F x≤G x) :
    finiteExpectation v F≤finiteExpectation v G :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (hv x))
end Linear
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators

lemma symbolCost_comm {A : Type*} (a b : A) : symbolCost a b=symbolCost b a := by
  classical
  simp only [symbolCost,eq_comm]
lemma nameCost_comm {A : Type*} {n : ℕ} (a b : Fin n → A) : nameCost a b=nameCost b a := by
  simp only [nameCost,symbolCost_comm]

lemma coupling_of_observation_lawClose {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q) {ε : ℝ}
    (h : LawClose (μ.map p) (ν.map q) ε) :
    ∃ R : MatrixCoupling (mass μ p) (mass ν q),R.cost symbolCost≤ε := by
  classical
  have : IsProbabilityMeasure (μ.map p) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (ν.map q) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  obtain ⟨r,hr,hrow,hcol,hcost⟩ := finite_coupling_of_lawClose (μ.map p) (ν.map q) h
  let R : MatrixCoupling (mass μ p) (mass ν q) := {
    weight := r
    nonneg := hr
    row := fun a => (hrow a).trans (map_measureReal_apply hp (measurableSet_singleton a))
    col := fun a => (hcol a).trans (map_measureReal_apply hq (measurableSet_singleton a)) }
  exact ⟨R,hcost⟩

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_ChunkNameCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open scoped BigOperators
lemma symbolCost_le_one {A : Type*} (a b : A) : symbolCost a b≤1 := by
  unfold symbolCost
  split <;> norm_num

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
namespace MatrixCoupling
variable {A B : Type*} [Fintype A] [Fintype B] {p : A → ℝ} {q : B → ℝ}
lemma cost_mono (r : MatrixCoupling p q) (d e : A → B → ℝ) (h : ∀ a b,d a b≤e a b) :
    r.cost d ≤ r.cost e :=
  Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ =>
    mul_le_mul_of_nonneg_left (h a b) (r.nonneg a b)))
lemma cost_affine (r : MatrixCoupling p q) (hp : ∑ a,p a=1) (K C : ℝ) (d : A → B → ℝ) :
    r.cost (fun a b => K*d a b+C)=K*r.cost d+C := by
  unfold cost
  simp only [mul_add,Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  · simp only [←Finset.sum_mul,r.row,hp,one_mul]
end MatrixCoupling

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_FiniteProductVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

lemma expectation_centered_sum_square (w : B → A → ℝ) (hw : ∀ b,∑ a,w b a=1)
    (f : B → A → ℝ) (hmean : ∀ b,∑ a,w b a*f b a=0) :
    finiteExpectation (productWeights w) (fun D => (∑ b,f b (D b))^2)=
      ∑ b,∑ a,w b a*(f b a)^2 := by
  have he (D : B → A) : (∑ b,f b (D b))^2=∑ b,∑ c,f b (D b)*f c (D c) := by
    rw [sq,Finset.sum_mul]
    simp only [Finset.mul_sum]
  simp_rw [he]
  rw [finiteExpectation_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [finiteExpectation_sum]
  calc
    _=finiteExpectation (productWeights w) (fun D => f b (D b)*f b (D b)) := by
      apply Finset.sum_eq_single b
      · intro c _ hcb
        rw [expectation_distinct_coordinates w hw b c (Ne.symm hcb),hmean,zero_mul]
      · simp
    _=∑ a,w b a*(f b a)^2 := by
      rw [expectation_coordinate w hw b (fun a => f b a*f b a)]
      simp only [pow_two]

lemma finiteExpectation_exists_le {E : Type*} [Fintype E] [Nonempty E]
    (v : E → ℝ) (hv : ∀ x,0≤v x) (hs : ∑ x,v x=1) (F : E → ℝ) :
    ∃ x,F x≤finiteExpectation v F := by
  classical
  obtain ⟨x,_,hx⟩ := Finset.exists_min_image (Finset.univ : Finset E) F Finset.univ_nonempty
  refine ⟨x,?_⟩
  calc
    F x=finiteExpectation v (fun _ => F x) := by rw [finiteExpectation_const,hs,one_mul]
    _≤finiteExpectation v F := finiteExpectation_mono v hv _ _ (fun y => hx y (Finset.mem_univ y))

lemma categorical_variance [DecidableEq A] (w : A → ℝ) (_hw : ∀ a,0≤w a)
    (hs : ∑ a,w a=1) (a : A) (q : ℝ) :
    (∑ z,w z*(q*((if z=a then 1 else 0)-w a))^2)≤q^2*w a := by
  have h1 : (∑ z,w z*(if z=a then 1 else 0))=w a := by simp
  have h2 : (∑ z,w z*(if z=a then 1 else 0)^2)=w a := by simp
  have he (z : A) : w z*(q*((if z=a then 1 else 0)-w a))^2=
      q^2*(w z*(if z=a then 1 else 0)^2)-
      (2*q^2*w a)*(w z*(if z=a then 1 else 0))+(q^2*(w a)^2)*w z := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,
    ←Finset.mul_sum,h1,h2,hs]
  nlinarith [sq_nonneg (q*w a)]

lemma categorical_mean_zero [DecidableEq A] (w : A → ℝ) (hs : ∑ a,w a=1) (a : A) (q : ℝ) :
    (∑ z,w z*(q*((if z=a then 1 else 0)-w a)))=0 := by
  have he (z : A) : w z*(q*((if z=a then 1 else 0)-w a))=
    q*(w z*(if z=a then 1 else 0))-(q*w a)*w z := by ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,hs]
  simp

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A]

omit [Nonempty A] in
lemma expected_row_error_square (q : B → ℝ) (w : B → A → ℝ)
    (hw : ∀ b a,0≤w b a) (hs : ∀ b,∑ a,w b a=1) (a : A) :
    finiteExpectation (productWeights w)
      (fun D => (assignedMass q D a-fractionalMass q w a)^2)≤∑ b,(q b)^2*w b a := by
  let f : B → A → ℝ := fun b z => q b*((if z=a then 1 else 0)-w b a)
  have he (D : B → A) : assignedMass q D a-fractionalMass q w a=∑ b,f b (D b) := by
    simp only [assignedMass,fractionalMass,f,mul_sub,Finset.sum_sub_distrib]
  simp_rw [he]
  rw [expectation_centered_sum_square w hs f (fun b => categorical_mean_zero (w b) (hs b) a (q b))]
  exact Finset.sum_le_sum (fun b _ => categorical_variance (w b) (hw b) (hs b) a (q b))

omit [Nonempty A] in
lemma expected_assignment_error_square (q : B → ℝ) (hq : ∀ b,0≤q b) (hqsum : ∑ b,q b=1)
    (w : B → A → ℝ) (hw : ∀ b a,0≤w b a) (hs : ∀ b,∑ a,w b a=1)
    {M : ℝ} (hM : ∀ b,q b≤M) :
    finiteExpectation (productWeights w) (fun D => assignmentError q w D^2)≤
      (Fintype.card A : ℝ)*M := by
  have hpt (D : B → A) : assignmentError q w D^2≤
      (Fintype.card A : ℝ)*∑ a,(assignedMass q D a-fractionalMass q w a)^2 := by
    simpa only [assignmentError,Finset.card_univ,sq_abs] using
      (sq_sum_le_card_mul_sum_sq (s:=Finset.univ)
        (f:=fun a => |assignedMass q D a-fractionalMass q w a|))
  have hW := productWeights_nonneg w hw
  calc
    _≤finiteExpectation (productWeights w)
        (fun D => (Fintype.card A : ℝ)*∑ a,(assignedMass q D a-fractionalMass q w a)^2) :=
      finiteExpectation_mono _ hW _ _ hpt
    _=(Fintype.card A : ℝ)*∑ a,finiteExpectation (productWeights w)
        (fun D => (assignedMass q D a-fractionalMass q w a)^2) := by
      rw [finiteExpectation_smul,finiteExpectation_sum]
    _≤(Fintype.card A : ℝ)*∑ a,∑ b,(q b)^2*w b a := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun a _ => expected_row_error_square q w hw hs a)
    _=(Fintype.card A : ℝ)*∑ b,(q b)^2 := by
      rw [Finset.sum_comm]
      simp only [←Finset.mul_sum,hs,mul_one]
    _≤(Fintype.card A : ℝ)*M := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      calc
        (∑ b,(q b)^2)≤∑ b,M*q b :=
          Finset.sum_le_sum (fun b _ => by nlinarith [mul_le_mul_of_nonneg_right (hM b) (hq b)])
        _=M := by rw [←Finset.mul_sum,hqsum,mul_one]

omit [DecidableEq A] [Nonempty A] in
lemma expected_assignment_cost (q : B → ℝ) (w : B → A → ℝ)
    (hs : ∀ b,∑ a,w b a=1) (c : A → B → ℝ) :
    finiteExpectation (productWeights w) (fun D => ∑ b,q b*c (D b) b)=
      ∑ b,∑ a,q b*w b a*c a b := by
  rw [finiteExpectation_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [finiteExpectation_smul,expectation_coordinate w hs b (fun a => c a b),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem exists_deterministic_assignment (q : B → ℝ) (hq : ∀ b,0≤q b) (hqsum : ∑ b,q b=1)
    (w : B → A → ℝ) (hw : ∀ b a,0≤w b a) (hs : ∀ b,∑ a,w b a=1)
    (c : A → B → ℝ) {M : ℝ} (hM : ∀ b,q b≤M) :
    ∃ D : B → A,assignmentError q w D^2+(∑ b,q b*c (D b) b)≤
      (Fintype.card A : ℝ)*M+∑ b,∑ a,q b*w b a*c a b := by
  obtain ⟨D,hD⟩ := finiteExpectation_exists_le (productWeights w) (productWeights_nonneg w hw)
    (productWeights_sum w hs)
    (fun D => assignmentError q w D^2+∑ b,q b*c (D b) b)
  refine ⟨D,hD.trans ?_⟩
  rw [finiteExpectation_add,expected_assignment_cost q w hs c]
  have h := expected_assignment_error_square q hq hqsum w hw hs hM
  linarith

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A]
namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ}

omit [DecidableEq B] in
lemma conditionalAssignment_nonneg (r : MatrixCoupling p q) (b : B) (a : A) :
    0 ≤ r.conditionalAssignment b a := by
  unfold conditionalAssignment
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact div_nonneg (r.nonneg a b) (r.right_nonneg b)

omit [DecidableEq B] in
lemma conditionalAssignment_sum (r : MatrixCoupling p q) (b : B) :
    ∑ a,r.conditionalAssignment b a=1 := by
  unfold conditionalAssignment
  by_cases hq : q b=0
  · simp [hq]
  · simp only [hq,ite_false,←Finset.sum_div,r.col,div_self hq]

omit [DecidableEq B] in
lemma mul_conditionalAssignment (r : MatrixCoupling p q) (a : A) (b : B) :
    q b*r.conditionalAssignment b a=r.weight a b := by
  unfold conditionalAssignment
  by_cases hq : q b=0
  · have hr : r.weight a b=0 := le_antisymm (by simpa only [hq] using r.le_right a b) (r.nonneg a b)
    simp [hq,hr]
  · simp only [hq,ite_false]
    exact mul_div_cancel₀ _ hq

omit [DecidableEq B] in
lemma fractionalMass_conditionalAssignment (r : MatrixCoupling p q) (a : A) :
    fractionalMass q r.conditionalAssignment a=p a := by
  simp only [fractionalMass,r.mul_conditionalAssignment,r.row]

theorem exists_rounded_decoder (r : MatrixCoupling p q) (hq : ∑ b,q b=1)
    (c : A → B → ℝ) {M : ℝ} (hM : ∀ b,q b≤M) :
    ∃ D : B → A,(∑ a,|assignedMass q D a-p a|)^2+(∑ b,q b*c (D b) b)≤
      (Fintype.card A : ℝ)*M+r.cost c := by
  obtain ⟨D,hD⟩ := exists_deterministic_assignment q r.right_nonneg hq r.conditionalAssignment
    r.conditionalAssignment_nonneg r.conditionalAssignment_sum c hM
  refine ⟨D,?_⟩
  simp only [assignmentError,r.fractionalMass_conditionalAssignment,r.mul_conditionalAssignment] at hD
  rw [Finset.sum_comm] at hD
  exact hD

end MatrixCoupling
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A]

omit [Fintype A] [DecidableEq B] [Nonempty A] in
lemma assignedMass_nonneg (q : B → ℝ) (hq : ∀ b,0≤q b) (D : B → A) (a : A) :
    0≤assignedMass q D a := Finset.sum_nonneg (fun b _ => mul_nonneg (hq b) (by split_ifs <;> norm_num))
omit [DecidableEq B] [Nonempty A] in
lemma assignedMass_sum (q : B → ℝ) (D : B → A) : ∑ a,assignedMass q D a=∑ b,q b := by
  unfold assignedMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ}

omit [DecidableEq B] [Nonempty A] in
lemma assignment_cost (q : B → ℝ) (hq : ∀ b,0≤q b) (D : B → A) (c : A → B → ℝ) :
    (assignment q hq D).cost c=∑ b,q b*c (D b) b := by
  unfold cost assignment
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp

omit [DecidableEq B] [Nonempty A] in
theorem repair_assignment (r : MatrixCoupling p q) (hq : ∑ b,q b=1)
    (D : B → A) (c : A → B → ℝ) (hc0 : ∀ a b,0 ≤ c a b) (hc1 : ∀ a b,c a b≤1) :
    ∃ R : MatrixCoupling p q,
      R.cost (fun a b => symbolCost a (D b))≤∑ a,|assignedMass q D a-p a| ∧
      R.cost c≤(∑ b,q b*c (D b) b)+∑ a,|assignedMass q D a-p a| := by
  have hp : ∑ a,p a=1 := by
    simp only [←r.row]
    rw [Finset.sum_comm]
    simp only [r.col,hq]
  obtain ⟨w,hw,hrow,hcol,hwcost⟩ := finite_maximal_coupling p (assignedMass q D) r.left_nonneg
    (assignedMass_nonneg q r.right_nonneg D) hp (by rw [assignedMass_sum,hq])
  let S : MatrixCoupling p (assignedMass q D) := ⟨w,hw,hrow,hcol⟩
  let U := assignment q r.right_nonneg D
  have hScost : S.cost symbolCost=(∑ a,∑ b,w a b*(if a=b then 0 else 1)) := by
    unfold cost
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : a=b <;> simp [S,symbolCost,h]
  have hS : S.cost symbolCost≤∑ a,|assignedMass q D a-p a| := by
    rw [hScost]
    apply hwcost.le.trans
    apply Finset.sum_le_sum
    intro a _
    have h : max (p a-assignedMass q D a) 0≤|p a-assignedMass q D a| :=
      max_le (le_abs_self _) (abs_nonneg _)
    simpa only [abs_sub_comm] using h
  have hU : U.cost (fun a b => symbolCost a (D b))=0 := by
    rw [assignment_cost]
    simp only [symbolCost_self,mul_zero,Finset.sum_const_zero]
  refine ⟨S.comp U,?_,?_⟩
  · have h := comp_cost_le S U symbolCost (fun a b => symbolCost a (D b))
      (fun a b => symbolCost a (D b)) (fun a b v => symbolCost_triangle a b (D v))
    rw [hU,add_zero] at h
    exact h.trans hS
  · have htri (a a' : A) (b : B) : c a b≤ symbolCost a a'+c a' b := by
      by_cases h : a=a'
      · subst a'; simp only [symbolCost_self,zero_add,le_refl]
      · simp only [symbolCost,ite_eq_right h]
        have h0 := hc0 a' b
        have h1 := hc1 a b
        linarith
    have h := comp_cost_le S U symbolCost c c htri
    rw [assignment_cost] at h
    linarith

end MatrixCoupling
end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_TypicalWordCodebook
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
lemma productWordWeight_sum (p : A → ℝ) (hp : ∑ a,p a=1) (n : ℕ) :
    (∑ w : Fin n → A,productWordWeight p n w)=1 :=
  productWeights_sum (fun _ : Fin n => p) (fun _ => hp)

omit [Fintype A] [DecidableEq A] in
lemma productWordWeight_nonneg (p : A → ℝ) (hp : ∀ a,0≤p a) (n : ℕ) (w : Fin n → A) :
    0≤productWordWeight p n w := Finset.prod_nonneg (fun i _ => hp (w i))

omit [Fintype A] [DecidableEq A] in
lemma productWordWeight_eq_exp (p : A → ℝ) {n : ℕ} (w : Fin n → A)
    (hw : ∀ i,0<p (w i)) : productWordWeight p n w=Real.exp (-wordInformation p w) := by
  rw [wordInformation,←Finset.sum_neg_distrib]
  simp only [neg_neg,Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact (Real.exp_log (hw i)).symm

omit [DecidableEq A] in
theorem information_codebook_card (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1)
    (n : ℕ) (L : ℝ) :
    let S := Finset.univ.filter (fun w : Fin n → A => (∀ i,0<p (w i)) ∧ wordInformation p w≤L)
    (S.card : ℝ)≤Real.exp L := by
  intro S
  have hweights (w : Fin n → A) (hw : w∈S) : Real.exp (-L)≤productWordWeight p n w := by
    obtain ⟨hpos,hinfo⟩ := (Finset.mem_filter.mp hw).2
    rw [productWordWeight_eq_exp p w hpos]
    exact Real.exp_le_exp.mpr (neg_le_neg hinfo)
  have hmass : (S.card : ℝ)*Real.exp (-L)≤1 := by
    calc
      _=∑ _w∈S,Real.exp (-L) := by simp
      _≤∑ w∈S,productWordWeight p n w := Finset.sum_le_sum hweights
      _≤∑ w : Fin n → A,productWordWeight p n w :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun w _ _ => productWordWeight_nonneg p hp n w)
      _=1 := productWordWeight_sum p hs n
  have h := mul_le_mul_of_nonneg_right hmass (Real.exp_pos L).le
  rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one,one_mul] at h
  exact h

section Ergodic
variable {X : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure X) [IsProbabilityMeasure μ]

omit [Fintype A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [IsProbabilityMeasure μ] in
lemma wordInformation_word (f : X → X) (p : X → A) (n : ℕ) (x : X) :
    wordInformation (mass μ p) (word f p n x)=birkhoffSum f (information μ p) n x := by
  simp only [wordInformation,word,information,birkhoffSum]
  exact Fin.sum_univ_eq_sum_range (fun i => -Real.log (mass μ p (p (f^[i] x)))) n

omit [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A] [IsProbabilityMeasure μ] in
lemma information_uniform_bound (p : X → A) (x : X) :
    |information μ p x|≤∑ a : A,|Real.log (mass μ p a)| := by
  simp only [information,abs_neg]
  exact Finset.single_le_sum (fun a _ => abs_nonneg (Real.log (mass μ p a))) (Finset.mem_univ (p x))

omit [DecidableEq A] in
theorem eventually_upper_information_codebook (f : X → X) (hf : Ergodic f μ)
    (p : X → A) (hp : Measurable p) {δ ε : ℝ} (hδ : 0<δ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∃ S : Finset (Fin n → A),
      (S.card : ℝ)≤Real.exp ((n : ℝ)*(obs μ p+δ)) ∧
      μ.real {x | word f p n x∉S}<ε := by
  have hC : 0≤∑ a : A,|Real.log (mass μ p a)| := Finset.sum_nonneg (fun a _ => abs_nonneg _)
  have hav := ergodic_L1_bounded hf (information_measurable μ p hp) hC (information_uniform_bound μ p)
  rw [integral_information μ p hp] at hav
  have hsmall := (tendsto_order.mp hav).2 (δ*ε) (mul_pos hδ hε)
  filter_upwards [hsmall,eventually_gt_atTop 0] with n hsmall hn
  let S := Finset.univ.filter (fun w : Fin n → A =>
    (∀ i,0 < mass μ p (w i)) ∧ wordInformation (mass μ p) w≤(n : ℝ)*(obs μ p+δ))
  refine ⟨S,information_codebook_card _ (mass_nonneg μ p) (by simpa using mass_sum μ p hp) n _,?_⟩
  have hpos : ∀ᵐ x ∂μ,∀ i : Fin n,0 < mass μ p (p (f^[i.val] x)) := by
    apply ae_all_iff.mpr
    intro i
    exact (hf.toMeasurePreserving.iterate i.val).quasiMeasurePreserving.ae (ae_mass_positive μ p)
  have hnpos : 0<(n : ℝ) := Nat.cast_pos.mpr hn
  have hsub : ∀ᵐ x ∂μ,word f p n x∉S → δ≤|orbitAverage f (information μ p) n x-obs μ p| := by
    filter_upwards [hpos] with x hx hbad
    have hi : (n : ℝ)*(obs μ p+δ)<wordInformation (mass μ p) (word f p n x) := by
      by_contra h
      exact hbad (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx,le_of_not_gt h⟩)
    rw [wordInformation_word] at hi
    have hb : obs μ p+δ<orbitAverage f (information μ p) n x := (lt_div_iff₀ hnpos).mpr (by simpa only [mul_comm] using hi)
    exact le_trans (by linarith) (le_abs_self _)
  have hi : Integrable (fun x => |orbitAverage f (information μ p) n x-obs μ p|) μ :=
    ((orbitAverage_integrable hf.toMeasurePreserving (information_integrable μ p hp) n).sub
      (integrable_const _)).abs
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ:=μ)
    (f:=fun x => |orbitAverage f (information μ p) n x-obs μ p|)
    (ae_of_all _ (fun x => abs_nonneg _)) hi δ
  have hmono : μ.real {x | word f p n x∉S}≤
      μ.real {x | δ≤|orbitAverage f (information μ p) n x-obs μ p|} :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
  have hb := mul_le_mul_of_nonneg_left hmono hδ.le
  nlinarith

end Ergodic
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
lemma weightInformation_centered (p : A → ℝ) (hs : ∑ a,p a=1) :
    (∑ a,p a*(-Real.log (p a)-weightEntropy p))=0 := by
  simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hs,one_mul,weightEntropy]
  ring

omit [DecidableEq A] in
lemma wordInformation_centered (p : A → ℝ) (n : ℕ) (w : Fin n → A) :
    wordInformation p w-(n : ℝ)*weightEntropy p=
      ∑ i : Fin n,(-Real.log (p (w i))-weightEntropy p) := by
  simp [wordInformation,Finset.sum_sub_distrib]

omit [DecidableEq A] in
lemma wordInformation_variance (p : A → ℝ) (hs : ∑ a,p a=1) (n : ℕ) :
    (∑ w : Fin n → A,productWordWeight p n w *
      (wordInformation p w-(n : ℝ)*weightEntropy p)^2)=(n : ℝ)*informationVariance p := by
  simp_rw [wordInformation_centered]
  have h := expectation_centered_sum_square (fun _ : Fin n => p) (fun _ => hs)
    (fun _ a => -Real.log (p a)-weightEntropy p) (fun _ => weightInformation_centered p hs)
  simpa only [finiteExpectation,productWeights,productWordWeight,informationVariance,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h

omit [Fintype A] [DecidableEq A] in
lemma productWordWeight_le_exp (p : A → ℝ) (hp : ∀ a,0≤p a) {n : ℕ}
    (w : Fin n → A) {L : ℝ} (hI : L≤wordInformation p w) :
    productWordWeight p n w≤Real.exp (-L) := by
  by_cases hpos : ∀ i,0<p (w i)
  · rw [productWordWeight_eq_exp p w hpos]
    exact Real.exp_le_exp.mpr (neg_le_neg hI)
  · push Not at hpos
    obtain ⟨i,hi⟩ := hpos
    have hz := le_antisymm hi (hp (w i))
    have hw : productWordWeight p n w=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact hz
    rw [hw]
    exact (Real.exp_pos _).le

omit [DecidableEq A] in
lemma iid_bad_information_mass (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1)
    (n : ℕ) {δ : ℝ} (hδ : 0<δ) :
    (∑ w : Fin n → A,if wordInformation p w<(n : ℝ)*(weightEntropy p-δ)
      then productWordWeight p n w else 0)*((n : ℝ)*δ)^2 ≤
      (n : ℝ)*informationVariance p := by
  rw [←wordInformation_variance p hs n,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro w _
  split_ifs with hw
  · have hdev : (n : ℝ)*δ< -(wordInformation p w-(n : ℝ)*weightEntropy p) := by nlinarith
    have hnd : 0≤(n : ℝ)*δ := mul_nonneg (Nat.cast_nonneg n) hδ.le
    apply mul_le_mul_of_nonneg_left _ (productWordWeight_nonneg p hp n w)
    nlinarith
  · simp only [zero_mul]
    exact mul_nonneg (productWordWeight_nonneg p hp n w) (sq_nonneg _)

theorem eventually_iid_typical_words (p : A → ℝ) (hp : ∀ a,0≤p a)
    (hs : ∑ a,p a=1) {δ ε : ℝ} (hδ : 0<δ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∃ T : Finset (Fin n → A),
      (∀ w∈T,productWordWeight p n w≤Real.exp (-(n : ℝ)*(weightEntropy p-δ))) ∧
      (∑ w : Fin n → A,if w∉T then productWordWeight p n w else 0)<ε := by
  have hV : 0 ≤ informationVariance p :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (hp a) (sq_nonneg _))
  obtain ⟨N,hN⟩ := exists_nat_gt (informationVariance p/(ε*δ^2))
  filter_upwards [eventually_ge_atTop N,eventually_gt_atTop 0] with n hn hn0
  let T := Finset.univ.filter (fun w : Fin n → A => (n : ℝ)*(weightEntropy p-δ)≤wordInformation p w)
  refine ⟨T,?_,?_⟩
  · intro w hw
    have h := productWordWeight_le_exp p hp w (Finset.mem_filter.mp hw).2
    simpa only [neg_mul] using h
  · have ht (w : Fin n → A) : w∉T ↔ wordInformation p w<(n : ℝ)*(weightEntropy p-δ) := by
      simp only [T,Finset.mem_filter,Finset.mem_univ,true_and,not_le]
    simp_rw [ht]
    have hb := iid_bad_information_mass p hp hs n hδ
    have hnpos : 0<(n : ℝ) := Nat.cast_pos.mpr hn0
    have hnN : (N : ℝ)≤n := by exact_mod_cast hn
    have hlarge : informationVariance p<ε*δ^2*(n : ℝ) := by
      have h := (div_lt_iff₀ (mul_pos hε (sq_pos_of_pos hδ))).mp (hN.trans_le hnN)
      nlinarith
    have hh := mul_lt_mul_of_pos_left hlarge hnpos
    have hsq : 0<((n : ℝ)*δ)^2 := sq_pos_of_pos (mul_pos hnpos hδ)
    nlinarith

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

lemma finiteWeightLaw_singleton (p : A → ℝ) (a : A) :
    finiteWeightLaw p {a}=ENNReal.ofReal (p a) := by
  classical
  simp [finiteWeightLaw,Measure.finsetSum_apply,Measure.smul_apply,Pi.single_apply]

omit [MeasurableSingletonClass A] in
lemma finiteWeightLaw_probability (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1) :
    IsProbabilityMeasure (finiteWeightLaw p) := by
  constructor
  simp only [finiteWeightLaw,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul,
    Measure.dirac_apply_of_mem (mem_univ _),mul_one]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun a _ => hp a),hs,ENNReal.ofReal_one]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iidShift_iterate (w : ℤ → A) (n : ℕ) (i : ℤ) :
    (iidShift^[n]) w i=w (i+n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (iidShift^[n]) w (i+1)=_
    rw [ih]
    congr 1
    push_cast
    ring

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iidShift_preserving (β : Measure A) [IsProbabilityMeasure β] :
    MeasurePreserving (iidShift (A:=A)) (Measure.infinitePi (fun _ : ℤ => β))
      (Measure.infinitePi (fun _ : ℤ => β)) := by
  refine ⟨iidShift.measurable,?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun i j : ℤ => by omega)

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_word_eq (n : ℕ) (w : ℤ → A) :
    word iidShift (fun z : ℤ → A => z 0) n w=fun i : Fin n => w i.val := by
  funext i
  change (iidShift^[i.val]) w 0=_
  rw [iidShift_iterate,zero_add]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_word_law (β : Measure A) [IsProbabilityMeasure β] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℤ => β)).map (word iidShift (fun z : ℤ → A => z 0) n)=
      Measure.pi (fun _ : Fin n => β) := by
  have hi : Function.Injective (fun i : Fin n => (i.val : ℤ)) := by
    intro i j h
    apply Fin.ext
    change (i.val : ℤ)=(j.val : ℤ) at h
    exact Int.ofNat_inj.mp h
  simpa only [funext (iid_word_eq (A:=A) n),Measure.infinitePi_eq_pi] using
    (Measure.map_infinitePi_infinitePi_of_inj (P:=fun _ : ℤ => β) hi)

lemma iid_word_mass (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1)
    (n : ℕ) (w : Fin n → A) :
    mass (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p))
      (word iidShift (fun z : ℤ → A => z 0) n) w=productWordWeight p n w := by
  let : IsProbabilityMeasure (finiteWeightLaw p) := finiteWeightLaw_probability p hp hs
  change (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p)).real
    ((word iidShift (fun z : ℤ → A => z 0) n) ⁻¹' {w})=_
  rw [←map_measureReal_apply (word_measurable iidShift iidShift.measurable _
    (measurable_pi_apply 0) n) (measurableSet_singleton w)]
  rw [iid_word_law,Measure.real,Measure.pi_singleton]
  simp only [finiteWeightLaw_singleton,ENNReal.toReal_prod,ENNReal.toReal_ofReal (hp _),productWordWeight]

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_FiniteBinCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

omit [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma wordPack_apply (f : Ω → Ω) (p : Ω → α) (n m : ℕ) (x : Ω) :
    wordPack n m (word f p (n*m) x)=word (f^[m]) (word f p m) n x := by
  funext i j
  simp only [wordPack,Equiv.trans_apply,Equiv.curry_apply,word]
  change p (f^[j.val+m*i.val] x)=p (f^[j.val] ((f^[m])^[i.val] x))
  rw [Function.iterate_add_apply,Function.iterate_mul]

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_EntropyRateCodebook
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [Fintype A] [DecidableEq A]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  (μ : Measure X) [IsProbabilityMeasure μ]

omit [DecidableEq A] in
theorem entropy_rate_codebook (f : X → X) (hf : MeasurePreserving f μ μ)
    (htotal : ∀ (m : ℕ), 0 < m → Ergodic (f^[m]) μ)
    (p : X → A) (hp : Measurable p) {δ : ℝ} (hδ : 0<δ) :
    ∃ m : ℕ, 0 < m ∧ ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
      ∃ S : Finset (Fin (n*m) → A),
        (S.card : ℝ)≤Real.exp ((n*m : ℕ)*(rate μ f p+δ)) ∧
        μ.real {x | word f p (n*m) x∉S}<ε := by
  have hlim := (tendsto_order.mp (rate_tendsto μ f hf p hp)).2
    (rate μ f p+δ/2) (by linarith)
  obtain ⟨m,hm,hmrate⟩ := (eventually_gt_atTop 0 |>.and hlim).exists
  have hmr : 0<(m : ℝ) := Nat.cast_pos.mpr hm
  have hblock : obs μ (word f p m)<(m : ℝ)*(rate μ f p+δ/2) := by
    exact (div_lt_iff₀ hmr).mp hmrate |>.trans_eq (mul_comm _ _)
  refine ⟨m,hm,?_⟩
  intro ε hε
  have htyp := eventually_upper_information_codebook μ (f^[m]) (htotal m hm)
    (word f p m) (word_measurable f hf.measurable p hp m)
    (δ:=(m : ℝ)*δ/2) (by positivity) hε
  filter_upwards [htyp] with n hn
  obtain ⟨B,hB,hbad⟩ := hn
  let S := B.map (wordPack n m).symm.toEmbedding
  have hmem (w : Fin (n*m) → A) : w∈S ↔ wordPack n m w∈B := by
    simp only [S,Finset.mem_map,Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨b,hb,rfl⟩
      simpa using hb
    · intro hw
      exact ⟨wordPack n m w,hw,(wordPack n m).symm_apply_apply w⟩
  refine ⟨S,?_,?_⟩
  · have hcard : S.card=B.card := Finset.card_map _
    rw [hcard]
    apply hB.trans (Real.exp_le_exp.mpr ?_)
    have hn0 : (0 : ℝ)≤n := Nat.cast_nonneg n
    push_cast
    nlinarith
  · convert hbad using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext x
    simp only [mem_ofPred_eq,hmem,wordPack_apply]

end HyperbolicCoding

end
section
namespace HyperbolicCoding.Marker
open scoped BigOperators
variable {A C : Type*} {n r : ℕ}

lemma column_centeredWindow (a : ℤ → A) (i t j : Fin n) :
    column (centeredWindow n a i) t j = a ((i.val : ℤ)-(t.val : ℤ)+(j.val : ℤ)) := by
  unfold column centeredWindow
  congr 1
  rw [Nat.cast_add,Nat.cast_sub (by omega : t.val≤n)]
  ring

lemma self_column_centeredWindow (a : ℤ → A) (i : Fin n) :
    column (centeredWindow n a i) i = fun j : Fin n => a (j.val : ℤ) := by
  funext j
  rw [column_centeredWindow,sub_self,zero_add]

lemma mem_candidates (hr : r < n) (zero one : A) (v : Fin (2*n) → A) (t : Fin n) :
    t∈candidates hr zero one v ↔ HeadMarker hr zero one (column v t) := by
  classical
  simp [candidates]

lemma phase_eq_of_no_earlier (hn : 0 < n) (hr : r < n) (zero one : A) (v : Fin (2*n) → A)
    (i : Fin n) (hi : HeadMarker hr zero one (column v i))
    (hbefore : ∀ t : Fin n,t < i → ¬HeadMarker hr zero one (column v t)) :
    phase hn hr zero one v=i := by
  classical
  have hm : i∈candidates hr zero one v := (mem_candidates hr zero one v i).mpr hi
  have hs : (candidates hr zero one v).Nonempty := ⟨i,hm⟩
  rw [phase,dite_eq_left hs]
  apply le_antisymm (Finset.min'_le _ _ hm)
  by_contra h
  have ht : (candidates hr zero one v).min' hs < i := lt_of_not_ge h
  exact hbefore _ ht ((mem_candidates hr zero one v _).mp (Finset.min'_mem _ hs))

theorem phase_centeredWindow (hn : 0 < n) (hr : r < n) (zero one : A) (h01 : zero≠one)
    (a : ℤ → A) (hblock : MarkedBlock hr zero one (fun j : Fin n => a (j.val : ℤ)))
    (i : Fin n) : phase hn hr zero one (centeredWindow n a i)=i := by
  apply phase_eq_of_no_earlier hn hr zero one _ i
  · rw [self_column_centeredWindow]
    exact hblock.1
  · intro t ht hm
    have hti : t.val < i.val := ht
    let j : Fin n := ⟨i.val-t.val,by omega⟩
    have hj : 0 < j.val := by dsimp [j]; omega
    obtain ⟨l,hl,hb⟩ := hblock.2 j hj
    have hz := hm.1 l
    rw [column_centeredWindow] at hz
    have heq : (i.val : ℤ)-(t.val : ℤ)+(l.val : ℤ) = ((j.val+l.val : ℕ) : ℤ) := by
      dsimp [j]
      omega
    rw [heq] at hz
    exact h01 (hz.symm.trans hb)

theorem decode_centeredWindow (hn : 0 < n) (hr : r < n) (zero one : A) (h01 : zero≠one)
    (D : (Fin n → A) → (Fin n → C)) (a : ℤ → A)
    (hblock : MarkedBlock hr zero one (fun j : Fin n => a (j.val : ℤ))) (i : Fin n) :
    decodeWindow hn hr zero one D (centeredWindow n a i)=D (fun j : Fin n => a (j.val : ℤ)) i := by
  unfold decodeWindow
  rw [phase_centeredWindow hn hr zero one h01 a hblock i,self_column_centeredWindow]

section Construction

lemma exists_multiple_window (hr : 0 < r) (j : ℕ) :
    ∃ k : ℕ,j≤k ∧ k < j+r ∧ k%r=0 := by
  by_cases hj : j%r=0
  · exact ⟨j,le_rfl,by omega,hj⟩
  · have hm : j%r < r := Nat.mod_lt j hr
    have he := Nat.mod_add_div j r
    refine ⟨j+(r-j%r),by omega,by omega,?_⟩
    have hk : j+(r-j%r)=r*(j/r+1) := by
      rw [Nat.mul_add,Nat.mul_one]
      omega
    rw [hk,Nat.mul_mod_right]

lemma exists_guard (hr0 : 0 < r) (hr : r < n) (j : Fin n) (hj : 0 < j.val) :
    ∃ k : Fin n, j.val≤k.val ∧ k.val < j.val+r ∧ r≤k.val ∧
      (k.val%r=0 ∨ k.val+1=n) := by
  by_cases hjr : j.val < r
  · exact ⟨⟨r,hr⟩,hjr.le,by dsimp only; omega,le_rfl,Or.inl (Nat.mod_self r)⟩
  · obtain ⟨k,hjk,hkr,hm⟩ := exists_multiple_window hr0 j.val
    by_cases hkn : k < n
    · exact ⟨⟨k,hkn⟩,hjk,hkr,(by dsimp only; omega),Or.inl hm⟩
    · refine ⟨⟨n-1,by omega⟩,by dsimp only; omega,by dsimp only; omega,by dsimp only; omega,Or.inr (by dsimp only; omega)⟩

theorem markWord_isMarked (hr0 : 0 < r) (hr : r < n) (zero one : A) (w : Fin n → A) :
    MarkedBlock hr zero one (markWord r zero one w) := by
  constructor
  · constructor
    · intro j
      simp only [markWord,j.isLt,↓reduceIte]
    · simp [markWord]
  · intro j hj
    obtain ⟨k,hjk,hkr,hrk,hk⟩ := exists_guard hr0 hr j hj
    let l : Fin r := ⟨k.val-j.val,by omega⟩
    have he : j.val+l.val=k.val := by dsimp [l]; omega
    refine ⟨l,by omega,?_⟩
    simp only [markWord,he,not_lt.mpr hrk,↓reduceIte,hk]

end Construction
end HyperbolicCoding.Marker

end
section
namespace HyperbolicCoding.Marker
open scoped BigOperators
variable {A : Type*} [Fintype A] [DecidableEq A] {n r : ℕ}

omit [Fintype A] [DecidableEq A] in
lemma markWord_eq_outside (zero one : A) (w : Fin n → A) (i : Fin n)
    (hi : i∉reserved n r) : markWord r zero one w i=w i := by
  simp only [reserved,Finset.mem_filter,Finset.mem_univ,true_and,not_or] at hi
  simp only [markWord,hi.1,hi.2.1,hi.2.2,or_self,↓reduceIte]

lemma reserved_card (_hr : 0 < r) : (reserved n r).card ≤ r+n/r+2 := by
  let F : reserved n r → (Fin r ⊕ (Fin (n/r+1) ⊕ Unit)) := fun i =>
    if hi : i.val.val < r then Sum.inl ⟨i.val.val,hi⟩
    else if hd : i.val.val%r=0 then Sum.inr (Sum.inl ⟨i.val.val/r,by
      have h := Nat.div_le_div_right (Nat.le_of_lt i.val.isLt) (c:=r)
      omega⟩)
    else Sum.inr (Sum.inr ())
  have hF : Function.Injective F := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    have hi := (Finset.mem_filter.mp i.property).2
    have hj := (Finset.mem_filter.mp j.property).2
    by_cases hi₀ : i.val.val < r
    · by_cases hj₀ : j.val.val < r
      · simpa [F,hi₀,hj₀] using hij
      · simp only [F,dite_eq_left hi₀,dite_eq_right hj₀] at hij
        split_ifs at hij
    · by_cases hj₀ : j.val.val < r
      · simp only [F,dite_eq_right hi₀,dite_eq_left hj₀] at hij
        split_ifs at hij
      · by_cases hi₁ : i.val.val%r=0
        · by_cases hj₁ : j.val.val%r=0
          · have hquot : i.val.val/r=j.val.val/r := by
              simpa [F,hi₀,hj₀,hi₁,hj₁] using hij
            have hq1 := Nat.mod_add_div i.val.val r
            have hq2 := Nat.mod_add_div j.val.val r
            rw [hquot] at hq1
            omega
          · simp [F,hi₀,hj₀,hi₁,hj₁] at hij
        · by_cases hj₁ : j.val.val%r=0
          · simp [F,hi₀,hj₀,hi₁,hj₁] at hij
          · omega
  have h := Fintype.card_le_of_injective F hF
  simpa only [Fintype.card_coe,Fintype.card_sum,Fintype.card_fin,Fintype.card_unit,
    ←Nat.add_assoc] using h

omit [Fintype A] [DecidableEq A] in
lemma markWord_cost (zero one : A) (w : Fin n → A) :
    nameCost w (markWord r zero one w) ≤ (reserved n r).card := by
  calc
    _ ≤ ∑ i : Fin n,if i∈reserved n r then (1 : ℝ) else 0 := by
      unfold nameCost
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i∈reserved n r
      · simp only [ite_eq_left hi]
        exact symbolCost_le_one _ _
      · rw [ite_eq_right hi,markWord_eq_outside zero one w i hi]
        simp [symbolCost]
    _ = _ := by simp

lemma overwrite_fiber_card (S : Finset (Fin n)) (f : (Fin n → A) → (Fin n → A))
    (hf : ∀ w i,i∉S → f w i=w i) (v : Fin n → A) :
    Fintype.card {w : Fin n → A // f w=v} ≤ (Fintype.card A)^S.card := by
  let F : {w : Fin n → A // f w=v} → (S → A) := fun w i => w.val i.val
  have hF : Function.Injective F := by
    intro w z hwz
    apply Subtype.ext
    funext i
    by_cases hi : i∈S
    · exact congrFun hwz ⟨i,hi⟩
    · calc
        w.val i = f w.val i := (hf w.val i hi).symm
        _ = v i := congrFun w.property i
        _ = f z.val i := (congrFun z.property i).symm
        _ = z.val i := hf z.val i hi
  simpa only [Fintype.card_fun,Fintype.card_coe] using Fintype.card_le_of_injective F hF

lemma markWord_fiber_card (zero one : A) (v : Fin n → A) :
    Fintype.card {w : Fin n → A // markWord r zero one w=v} ≤
      (Fintype.card A)^(reserved n r).card :=
  overwrite_fiber_card (reserved n r) (markWord r zero one)
    (markWord_eq_outside zero one) v

end HyperbolicCoding.Marker

end
section
namespace HyperbolicCoding
open Filter
open scoped Topology

lemma marked_entropy_exponent_bound (a h δ : ℝ) (ha : 1≤a) (K r m n : ℕ)
    (hr : 0 < r)
    (hδ : (2*(K : ℝ)+1)*δ≤h/4)
    (hguard : ((K : ℝ)+1)*Real.log a/(r : ℝ)≤h/4) :
    2*Real.exp ((n*K*m : ℕ)*(h+δ))*a^(Marker.reserved (n*K*m+n*m) r).card*
      Real.exp (-((n*K*m+n*m : ℕ) : ℝ)*(h-δ)) ≤
      2*Real.exp (((r : ℝ)+2)*Real.log a-(n : ℝ)*m*(h/2)) := by
  let k := n*K*m
  let N := n*K*m+n*m
  let d := (Marker.reserved N r).card
  have ha0 : 0<a := lt_of_lt_of_le zero_lt_one ha
  have hlog : 0≤Real.log a := Real.log_nonneg ha
  have hrr : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hd : (d : ℝ)≤(r : ℝ)+(N : ℝ)/r+2 := by
    have hd' : (d : ℝ)≤(r+N/r+2 : ℕ) := by exact_mod_cast Marker.reserved_card (n:=N) hr
    push_cast at hd'
    exact hd'.trans (by gcongr; exact Nat.cast_div_le)
  have he : (k : ℝ)*(h+δ)+(d : ℝ)*Real.log a-(N : ℝ)*(h-δ) ≤
      ((r : ℝ)+2)*Real.log a-(n : ℝ)*m*(h/2) := by
    calc
      _ ≤ (k : ℝ)*(h+δ)+((r : ℝ)+(N : ℝ)/r+2)*Real.log a-(N : ℝ)*(h-δ) := by gcongr
      _ = ((r : ℝ)+2)*Real.log a+(n : ℝ)*m*
          (-h+(2*(K : ℝ)+1)*δ+((K : ℝ)+1)*Real.log a/r) := by
        dsimp [k,N]
        push_cast
        field_simp
        ring
      _ ≤ _ := by
        have hh : -h+(2*(K : ℝ)+1)*δ+((K : ℝ)+1)*Real.log a/r ≤ -(h/2) := by linarith
        have hg := mul_le_mul_of_nonneg_left hh (show 0≤(n : ℝ)*m by positivity)
        linarith
  have hp : a^d=Real.exp ((d : ℝ)*Real.log a) := by rw [Real.exp_nat_mul,Real.exp_log ha0]
  change 2*Real.exp ((k : ℝ)*(h+δ))*a^d*Real.exp (-(N : ℝ)*(h-δ))≤_
  rw [hp,mul_assoc (2 : ℝ),mul_assoc (2 : ℝ),←Real.exp_add,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem exists_entropy_slack_parameters (a h ε : ℝ) (ha : 1≤a) (hh : 0<h) (hε : 0<ε) :
    ∃ K r : ℕ,0<K ∧ 0 < r ∧ ∃ δ : ℝ,0<δ ∧
      (1 : ℝ)/(K+1 : ℕ)<ε ∧
      ∀ m : ℕ, 0 < m → ∀ M : ℝ, 0 < M → ∀ᶠ n : ℕ in atTop,
        0<n ∧ r<n*K*m+n*m ∧
        ((n*m : ℕ) : ℝ)/(n*K*m+n*m : ℕ)<ε ∧
        ((Marker.reserved (n*K*m+n*m) r).card : ℝ)/(n*K*m+n*m : ℕ)<ε ∧
        2*Real.exp ((n*K*m : ℕ)*(h+δ))*a^(Marker.reserved (n*K*m+n*m) r).card*
          Real.exp (-((n*K*m+n*m : ℕ) : ℝ)*(h-δ))<M := by
  obtain ⟨K,hK⟩ := exists_nat_gt (max (1 : ℝ) (1/ε))
  have hKpos : 0<K := by exact_mod_cast lt_trans zero_lt_one ((le_max_left _ _).trans_lt hK)
  have hKR : 0<(K : ℝ)+1 := by positivity
  have htail : (1 : ℝ)/(K+1 : ℕ)<ε := by
    apply (div_lt_iff₀ (by positivity)).mpr
    have hg := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hK)
    push_cast
    nlinarith
  obtain ⟨r,hr⟩ := exists_nat_gt (max 1 (max (4*((K : ℝ)+1)*Real.log a/h) (4/ε)))
  have hrpos : 0 < r := by exact_mod_cast lt_trans zero_lt_one ((le_max_left _ _).trans_lt hr)
  have hrr : (0 : ℝ) < r := Nat.cast_pos.mpr hrpos
  have hguard : ((K : ℝ)+1)*Real.log a/r≤h/4 := by
    apply (div_le_iff₀ hrr).mpr
    have hg := (div_lt_iff₀ hh).mp
      ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hr))
    nlinarith
  have hrsmall : (1 : ℝ)/r<ε/4 := by
    apply (div_lt_iff₀ hrr).mpr
    have hg := (div_lt_iff₀ hε).mp
      ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hr))
    nlinarith
  let δ : ℝ := h/(8*((K : ℝ)+1))
  have hδpos : 0<δ := div_pos hh (by positivity)
  have hδ : (2*(K : ℝ)+1)*δ≤h/4 := by
    have heq : (8*((K : ℝ)+1))*δ=h := by dsimp [δ]; field_simp
    have hg : 0≤δ := hδpos.le
    nlinarith
  refine ⟨K,r,hKpos,hrpos,δ,hδpos,htail,?_⟩
  intro m hm M hM
  let C := ((r : ℝ)+2)*Real.log a
  obtain ⟨n₀,hn₀⟩ := exists_nat_gt (max ((r : ℝ)+1)
    (max (4*((r : ℝ)+2)/ε) (2*(C-Real.log (M/2))/h)))
  filter_upwards [eventually_ge_atTop n₀] with n hn
  have hnr : (n₀ : ℝ)≤n := by exact_mod_cast hn
  have hlarge := hn₀.trans_le hnr
  have hnr' : (r : ℝ)+1<(n : ℝ) := (le_max_left _ _).trans_lt hlarge
  have hnp : 0 < n := by
    exact_mod_cast (lt_trans (by positivity : (0 : ℝ)<(r : ℝ)+1) hnr')
  have hnm : n≤n*m := Nat.le_mul_of_pos_right n hm
  have hnN : n≤n*K*m+n*m := hnm.trans (Nat.le_add_left _ _)
  have hnNR : (n : ℝ)≤(n*K*m+n*m : ℕ) := by exact_mod_cast hnN
  have hnR : (0 : ℝ)<n := Nat.cast_pos.mpr hnp
  have hN : (0 : ℝ)<(n*K*m+n*m : ℕ) := hnR.trans_le hnNR
  refine ⟨hnp,?_,?_,?_,?_⟩
  · have : r<n := by exact_mod_cast (show (r : ℝ)<n by linarith)
    exact this.trans_le hnN
  · have hem : ((n*m : ℕ) : ℝ)/(n*K*m+n*m : ℕ)=(1 : ℝ)/(K+1 : ℕ) := by
      push_cast
      have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
      field_simp
    simpa only [hem] using htail
  · have hd : ((Marker.reserved (n*K*m+n*m) r).card : ℝ)≤
        (r : ℝ)+((n*K*m+n*m : ℕ) : ℝ)/r+2 := by
      have hd' : ((Marker.reserved (n*K*m+n*m) r).card : ℝ)≤(r+(n*K*m+n*m)/r+2 : ℕ) :=
        by exact_mod_cast Marker.reserved_card (n:=n*K*m+n*m) hrpos
      push_cast at hd'
      exact hd'.trans (by gcongr; exact Nat.cast_div_le)
    have hsmall : ((r : ℝ)+2)/((n*K*m+n*m : ℕ) : ℝ)<ε/4 := by
      apply (div_lt_iff₀ hN).mpr
      have ht := (div_lt_iff₀ hε).mp
        ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hlarge))
      have hg := mul_le_mul_of_nonneg_left hnNR hε.le
      nlinarith
    have hdivide := div_le_div_of_nonneg_right hd hN.le
    have heq : ((r : ℝ)+((n*K*m+n*m : ℕ) : ℝ)/r+2)/((n*K*m+n*m : ℕ) : ℝ)=
        ((r : ℝ)+2)/((n*K*m+n*m : ℕ) : ℝ)+(1 : ℝ)/r := by field_simp; ring
    rw [heq] at hdivide
    linarith
  · apply lt_of_le_of_lt (marked_entropy_exponent_bound a h δ ha K r m n hrpos hδ hguard)
    have ht := (div_lt_iff₀ hh).mp
      ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hlarge))
    have hnmR : (n : ℝ)≤(n : ℝ)*m := by exact_mod_cast hnm
    have hg := mul_le_mul_of_nonneg_right hnmR hh.le
    have hexp : C-(n : ℝ)*m*(h/2)<Real.log (M/2) := by nlinarith
    have he := Real.exp_lt_exp.mpr hexp
    rw [Real.exp_log (by positivity : 0<M/2)] at he
    change 2*Real.exp (C-(n : ℝ)*m*(h/2))<M
    linarith

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Towers_FiniteCouplingRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

omit [MeasurableSingletonClass B] in
theorem realize_finite_coupling_finite (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (p : X → A) (hp : Measurable p) (t : B → ℝ) (R : MatrixCoupling (mass μ p) t) :
    ∃ q : X → B,Measurable q ∧ ∀ a b,mass μ (fun x => (p x,q x)) (a,b)=R.weight a b := by
  have hh (a : A) : ∃ q : X → B,Measurable q ∧
      ∀ b,μ.real ((p ⁻¹' {a})∩q ⁻¹' {b})=R.weight a b :=
    exists_finite_random_variable μ (hp (measurableSet_singleton a)) (R.weight a) (R.nonneg a) (R.row a)
  choose q hq hqr using hh
  let q' : X → B := fun x => q (p x) x
  have hq' : Measurable q' := (measurable_from_prod_countable_right
    (f:=fun ax : A×X => q ax.1 ax.2) hq).comp (hp.prodMk measurable_id)
  refine ⟨q',hq',fun a b => ?_⟩
  have hset : (fun x => (p x,q' x)) ⁻¹' {(a,b)}=(p ⁻¹' {a})∩q a ⁻¹' {b} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq,mem_inter_iff,q']
    constructor
    · rintro ⟨ha,hb⟩
      exact ⟨ha,by simpa only [ha] using hb⟩
    · rintro ⟨ha,hb⟩
      exact ⟨ha,by simpa only [ha] using hb⟩
  simpa only [mass,hset,Measure.real] using hqr a b

omit [StandardBorelSpace X] [Nonempty B] in
lemma integral_cost_of_realization (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → A) (hp : Measurable p) (q : X → B) (hq : Measurable q)
    {t : B → ℝ} (R : MatrixCoupling (mass μ p) t)
    (hR : ∀ a b,mass μ (fun x => (p x,q x)) (a,b)=R.weight a b) (c : A → B → ℝ) :
    (∫ x,c (p x) (q x) ∂μ)=R.cost c := by
  rw [←sum_mass_mul_integral μ (fun x => (p x,q x)) (hp.prodMk hq) (fun ab => c ab.1 ab.2)]
  simp only [Fintype.sum_prod_type,hR,MatrixCoupling.cost]

omit [StandardBorelSpace X] in
lemma finite_symbolCost_integral (μ : Measure X) [IsFiniteMeasure μ]
    (p q : X → A) (hp : Measurable p) (hq : Measurable q) :
    (∫ x,symbolCost (p x) (q x) ∂μ)=μ.real {x | p x≠q x} := by
  have hm : MeasurableSet {x | p x≠q x} := (measurableSet_eq_fun hp hq).compl
  have he : (fun x => symbolCost (p x) (q x))={x | p x≠q x}.indicator (fun _ : X => (1 : ℝ)) := by
    funext x
    by_cases hx : p x=q x <;> simp [symbolCost,hx]
  rw [he]
  change (∫ x,{x | p x≠q x}.indicator (fun _ : X => (1 : ℝ)) x ∂μ)=_
  rw [integral_indicator hm]
  simp

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

omit [MeasurableSingletonClass B] in
theorem exists_independent_finite_phase (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (p : X → A) (hp : Measurable p) :
    ∃ q : X → B,Measurable q ∧ ∀ b : B,
      (μ.restrict (q ⁻¹' {b})).map p=(Fintype.card B : ℝ≥0∞)⁻¹ • μ.map p := by
  have hn : (Fintype.card B : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  let R : MatrixCoupling (mass μ p) (fun _ : B => (μ univ).toReal/(Fintype.card B : ℝ)) := {
    weight := fun a _ => mass μ p a/(Fintype.card B : ℝ)
    nonneg := fun a _ => div_nonneg (mass_nonneg μ p a) (Nat.cast_nonneg _)
    row := fun a => by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      exact mul_div_cancel₀ _ hn
    col := fun _ => by rw [←Finset.sum_div,mass_sum μ p hp] }
  obtain ⟨q,hq,hpq⟩ := realize_finite_coupling_finite μ p hp _ R
  refine ⟨q,hq,fun b => ?_⟩
  apply Measure.ext_of_singleton
  intro a
  have hfin : (Fintype.card B : ℝ≥0∞)⁻¹≠⊤ := by
    exact ENNReal.inv_ne_top.mpr (by exact_mod_cast Fintype.card_ne_zero)
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top hfin (measure_ne_top _ _))).mp
  rw [Measure.map_apply hp (measurableSet_singleton a),Measure.restrict_apply (hp (measurableSet_singleton a)),
    ENNReal.toReal_mul,Measure.map_apply hp (measurableSet_singleton a)]
  have he : p ⁻¹' {a}∩q ⁻¹' {b}=(fun x => (p x,q x)) ⁻¹' {(a,b)} := by
    ext x
    simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,Prod.mk.injEq]
  rw [he]
  change mass μ (fun x => (p x,q x)) (a,b)=_
  rw [hpq]
  change mass μ p a/(Fintype.card B : ℝ)=_
  rw [ENNReal.toReal_inv,ENNReal.toReal_natCast]
  exact div_eq_inv_mul _ _

omit [StandardBorelSpace X] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [MeasurableSingletonClass B] [Nonempty B] in
lemma finite_phase_factor {C : Type*} [MeasurableSpace C]
    (μ : Measure X) (p : X → A) (hp : Measurable p) (q : X → B) (b : B)
    (h : (μ.restrict (q ⁻¹' {b})).map p=(Fintype.card B : ℝ≥0∞)⁻¹ • μ.map p)
    (g : A → C) (hg : Measurable g) :
    (μ.restrict (q ⁻¹' {b})).map (g ∘ p)=(Fintype.card B : ℝ≥0∞)⁻¹ • μ.map (g ∘ p) := by
  rw [←Measure.map_map hg hp,h,Measure.map_smul,Measure.map_map hg hp]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
variable {X I A : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [Countable I] [MeasurableSpace A]

attribute [local instance] OAI.HyperbolicCoding.disjointIndexOptionMeasurableSpace
local instance disjointIndexOptionMeasurableSingletonClass : MeasurableSingletonClass (Option I) :=
  ⟨fun _ => trivial⟩

omit [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] in
lemma disjointIndex_some (s : I → Set X) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (x : X) (i : I) : disjointIndex s x=some i ↔ x∈s i := by
  classical
  unfold disjointIndex
  split_ifs with h
  · constructor
    · intro he
      have hi : h.choose=i := Option.some.inj he
      exact hi ▸ h.choose_spec
    · intro hx
      congr 1
      by_contra hne
      exact Set.disjoint_left.mp (hd hne) h.choose_spec hx
  · have hx : x∉s i := fun hx => h ⟨i,hx⟩
    simp [hx]

omit [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] in
lemma disjointIndex_none (s : I → Set X) (x : X) :
    disjointIndex s x=none ↔ x∉⋃ i,s i := by
  classical
  simp only [disjointIndex]
  split_ifs with h
  · have hx : x∈⋃ i,s i := mem_iUnion.mpr h
    simp [hx]
  · have hx : x∉⋃ i,s i := by simpa only [mem_iUnion] using h
    simp [hx]

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma measurable_disjointIndex (s : I → Set X) (hs : ∀ i,MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) : Measurable (disjointIndex s) := by
  apply measurable_to_countable'
  intro i
  cases i with
  | none =>
    have he : (disjointIndex s) ⁻¹' {none}=(⋃ i,s i)ᶜ := by
      ext x
      exact disjointIndex_none s x
    rw [he]
    exact (MeasurableSet.iUnion hs).compl
  | some i =>
    have he : (disjointIndex s) ⁻¹' {some i}=s i := by
      ext x
      exact disjointIndex_some s hd x i
    rw [he]
    exact hs i

omit [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I]
  [MeasurableSpace A] in
lemma disjointPaste_on (s : I → Set X) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (f : I → X → A) (f₀ : X → A) {i : I} {x : X} (hx : x∈s i) :
    disjointPaste s f f₀ x=f i x := by
  unfold disjointPaste
  rw [(disjointIndex_some s hd x i).mpr hx]
omit [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I]
  [MeasurableSpace A] in
lemma disjointPaste_off (s : I → Set X) (f : I → X → A) (f₀ : X → A)
    {x : X} (hx : x∉⋃ i,s i) : disjointPaste s f f₀ x=f₀ x := by
  unfold disjointPaste
  rw [(disjointIndex_none s x).mpr hx]

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma measurable_disjointPaste (s : I → Set X) (hs : ∀ i,MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (f : I → X → A)
    (hf : ∀ i,Measurable (f i)) (f₀ : X → A) (hf₀ : Measurable f₀) :
    Measurable (disjointPaste s f f₀) := by
  let F : Option I×X → A := fun ix => match ix.1 with
    | none => f₀ ix.2
    | some i => f i ix.2
  have hF : Measurable F := measurable_from_prod_countable_right (fun i => by
    cases i
    · exact hf₀
    · exact hf _)
  exact hF.comp ((measurable_disjointIndex s hs hd).prodMk measurable_id)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X : Type*} [MeasurableSpace X]

lemma measurableSet_entryLevel {T : X → X} (hT : Measurable T) {B : Set X}
    (hB : MeasurableSet B) (n : ℕ) : MeasurableSet (entryLevel T B n) := by
  have heq : entryLevel T B n=(T^[n] ⁻¹' B) ∩ ⋂ j : ℕ,⋂ (_ : j<n),(T^[j] ⁻¹' B)ᶜ := by
    ext x
    simp only [entryLevel,mem_ofPred_eq,mem_inter_iff,mem_iInter,mem_compl_iff,mem_preimage]
  rw [heq]
  exact (hB.preimage (hT.iterate n)).inter
    (MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ => (hB.preimage (hT.iterate j)).compl)))

omit [MeasurableSpace X] in
lemma entryLevel_disjoint (T : X → X) (B : Set X) {n m : ℕ} (hnm : n≠m) :
    Disjoint (entryLevel T B n) (entryLevel T B m) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hnm with h|h
  · exact hy.2 n h hx.1
  · exact hx.2 m h hy.1

omit [MeasurableSpace X] in
lemma mem_entryLevel_iterate {T : X → X} {B : Set X} {n i : ℕ} (hi : i≤n)
    {x : X} (hx : x∈entryLevel T B n) : T^[i] x∈entryLevel T B (n-i) := by
  constructor
  · simpa only [←Function.iterate_add_apply,Nat.sub_add_cancel hi] using hx.1
  · intro j hj
    rw [←Function.iterate_add_apply]
    exact hx.2 (j+i) (by omega)

lemma mem_entryLevel_back (e : X ≃ᵐ X) {B : Set X} {n j : ℕ} {x : X}
    (hx : x∈entryLevel e B n) (hpast : ∀ i : ℕ, (0 < i) → (i ≤ j) → e.symm^[i] x∉B) :
    e.symm^[j] x∈entryLevel e B (n+j) := by
  have hi : Function.LeftInverse (e : X → X) e.symm := e.apply_symm_apply
  constructor
  · rw [Function.iterate_add_apply,hi.iterate j x]
    exact hx.1
  · intro l hl
    by_cases hj : j≤l
    · have heq : l=(l-j)+j := by omega
      rw [heq,Function.iterate_add_apply,hi.iterate j x]
      exact hx.2 (l-j) (by omega)
    · have hlj : j=l+(j-l) := by omega
      rw [hlj,Function.iterate_add_apply,hi.iterate l]
      exact hpast (j-l) (by omega) (by omega)

lemma ae_exists_entry {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ) {B : Set X} (hB : MeasurableSet B) (hBp : 0<μ B) :
    ∀ᵐ x ∂μ,∃ n : ℕ,x∈entryLevel T B n := by
  classical
  let H : Set X := ⋃ n : ℕ,T^[n] ⁻¹' B
  have hH : MeasurableSet H := MeasurableSet.iUnion (fun n => hB.preimage (hT.measurable.iterate n))
  have hsub : T ⁻¹' H⊆H := by
    intro x hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n+1,by simpa only [mem_preimage,Function.iterate_succ_apply] using hn⟩
  have heq : T ⁻¹' H =ᵐ[μ] H := ae_eq_of_ae_subset_of_measure_ge
    (Filter.Eventually.of_forall hsub) (hT.toMeasurePreserving.measure_preimage hH.nullMeasurableSet).ge
    (hH.preimage hT.measurable).nullMeasurableSet (measure_ne_top μ H)
  have hp : 0<μ H := hBp.trans_le (measure_mono (fun x hx => mem_iUnion.mpr ⟨0,hx⟩))
  have hfull : ∀ᵐ x ∂μ,x∈H := by
    rcases hT.quasiErgodic.ae_mem_or_ae_notMem₀ hH.nullMeasurableSet heq with hh|hh
    · exact hh
    · have : μ H=0 := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hh
      exact (hp.ne' this).elim
  filter_upwards [hfull] with x hx
  have hex : ∃ n : ℕ,T^[n] x∈B := mem_iUnion.mp hx
  exact ⟨Nat.find hex,Nat.find_spec hex,fun j hj => Nat.find_min hex hj⟩

lemma measurableSet_entryTowerBase (e : X ≃ᵐ X) {B : Set X} (hB : MeasurableSet B) (N : ℕ) :
    MeasurableSet (entryTowerBase e B N) :=
  MeasurableSet.iUnion (fun _ => measurableSet_entryLevel e.measurable hB _)

lemma entryTower_disjoint (e : X ≃ᵐ X) (B : Set X) {N : ℕ} (hN : 0<N)
    (i j : Fin N) (hij : i≠j) :
    Disjoint ((e^[i.val]) '' entryTowerBase e B N) ((e^[j.val]) '' entryTowerBase e B N) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨y,hy,rfl⟩ ⟨z,hz,heq⟩
  obtain ⟨q,hq⟩ := mem_iUnion.mp hy
  obtain ⟨r,hr⟩ := mem_iUnion.mp hz
  have hqi : i.val≤q*N+(N-1) := by omega
  have hrj : j.val ≤ r*N+(N-1) := by omega
  have hx := mem_entryLevel_iterate hqi hq
  have hz := mem_entryLevel_iterate hrj hr
  rw [heq] at hz
  have he : q*N+(N-1)-i.val=r*N+(N-1)-j.val := by
    by_contra hne
    exact Set.disjoint_left.mp (entryLevel_disjoint e B hne) hx hz
  have hi : (q*N+(N-1)-i.val)%N=N-1-i.val := by
    rw [Nat.add_sub_assoc (by omega : i.val≤N-1),Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
  have hj : (r*N+(N-1)-j.val)%N=N-1-j.val := by
    rw [Nat.add_sub_assoc (by omega : j.val≤N-1),Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
  have hh := congrArg (fun n => n%N) he
  rw [hi,hj] at hh
  exact hij (Fin.ext (by omega))

lemma entryTower_covers (e : X ≃ᵐ X) (B : Set X) {N : ℕ} (hN : 0<N) {x : X}
    (hx : ∃ n : ℕ,x∈entryLevel e B n)
    (hpast : ∀ i : ℕ, (0 < i) → (i < N) → e.symm^[i] x∉B) :
    x∈⋃ j : Fin N,(e^[j.val]) '' entryTowerBase e B N := by
  obtain ⟨n,hn⟩ := hx
  let j := N-1-n%N
  have hj : j<N := by dsimp [j]; omega
  have hnum : n+j=(n/N)*N+(N-1) := by
    have hd := Nat.mod_add_div n N
    have hm := Nat.mod_lt n hN
    rw [Nat.mul_comm] at hd
    dsimp [j]
    omega
  apply mem_iUnion.mpr
  refine ⟨⟨j,hj⟩,e.symm^[j] x,?_,?_⟩
  · apply mem_iUnion.mpr
    refine ⟨n/N,?_⟩
    rw [←hnum]
    exact mem_entryLevel_back e hn (fun i hi hij => hpast i hi (hij.trans_lt hj))
  · exact (show Function.LeftInverse (e : X → X) e.symm from e.apply_symm_apply).iterate j x

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology BigOperators
variable {X : Type*} [MeasurableSpace X]

lemma measurableSet_iterate_image (e : X ≃ᵐ X) {U : Set X} (hU : MeasurableSet U) (j : ℕ) :
    MeasurableSet ((e^[j]) '' U) := by
  have hh := (iterateEquiv e j).measurableSet_image.mpr hU
  simpa only [funext (iterateEquiv_apply e j)] using hh

lemma entryTower_error {μ : Measure X} [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : Ergodic e μ) {B : Set X} (hB : MeasurableSet B) (hBp : 0<μ B)
    {N : ℕ} (hN : 0<N) :
    μ (⋃ j : Fin N,(e^[j.val]) '' entryTowerBase e B N)ᶜ≤(N : ℝ≥0∞)*μ B := by
  classical
  have hc : (⋃ j : Fin N,(e^[j.val]) '' entryTowerBase e B N)ᶜ ≤ᵐ[μ]
      (⋃ j : Fin N,(e.symm^[j.val]) ⁻¹' B) := by
    filter_upwards [ae_exists_entry he hB hBp] with x hx hnot
    by_contra hbad
    apply hnot
    apply entryTower_covers e B hN hx
    intro i _hi hiN hmem
    exact hbad (mem_iUnion.mpr ⟨⟨i,hiN⟩,hmem⟩)
  calc
    _≤μ (⋃ j : Fin N,(e.symm^[j.val]) ⁻¹' B) := measure_mono_ae hc
    _≤∑' j : Fin N,μ ((e.symm^[j.val]) ⁻¹' B) := measure_iUnion_le _
    _=(N : ℝ≥0∞)*μ B := by
      simp only [((he.toMeasurePreserving.symm e).iterate _).measure_preimage hB.nullMeasurableSet,
        tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

lemma exists_small_positive_marker [TopologicalSpace X] [SecondCountableTopology X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] {δ : ℝ≥0∞} (hδ : 0<δ) :
    ∃ B : Set X,MeasurableSet B ∧ 0<μ B ∧ μ B<δ := by
  obtain ⟨x,hx⟩ := μ.nonempty_support (by exact NeZero.ne μ)
  obtain ⟨B,hxB,hBm,hB⟩ := (Set.singleton x).exists_isOpen_lt_of_lt δ (by simpa using hδ : μ {x}<δ)
  exact ⟨B,hBm.measurableSet,(μ.mem_support_iff_forall x).mp hx B (hBm.mem_nhds (hxB (mem_singleton x))),hB⟩

theorem exists_rohlin_tower [TopologicalSpace X] [SecondCountableTopology X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular]
    (e : X ≃ᵐ X) (he : Ergodic e μ) {N : ℕ} (hN : 0<N) {ε : ℝ} (hε : 0<ε) :
    ∃ U : Set X,MeasurableSet U ∧
      (∀ i j : Fin N,i≠j → Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)) ∧
      μ (⋃ j : Fin N,(e^[j.val]) '' U)ᶜ<ENNReal.ofReal ε := by
  have hNc : (N : ℝ≥0∞)≠0 := by exact_mod_cast hN.ne'
  have hNf : (N : ℝ≥0∞)≠⊤ := by simp
  have hd : 0<ENNReal.ofReal ε/(N : ℝ≥0∞) := ENNReal.div_pos (ENNReal.ofReal_pos.mpr hε).ne' hNf
  obtain ⟨B,hB,hBp,hBs⟩ := exists_small_positive_marker μ hd
  refine ⟨entryTowerBase e B N,measurableSet_entryTowerBase e hB N,entryTower_disjoint e B hN,?_⟩
  apply (entryTower_error e he hB hBp hN).trans_lt
  rw [mul_comm]
  exact (ENNReal.lt_div_iff_mul_lt (Or.inl hNc) (Or.inl hNf)).mp hBs

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma measurable_paintTower (e : X ≃ᵐ X) {U : Set X} (hU : MeasurableSet U) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    {B : X → (Fin N → A)} (hB : Measurable B) {p : X → A} (hp : Measurable p) :
    Measurable (paintTower e U N B p) :=
  measurable_disjointPaste (fun i : Fin N => (e^[i.val]) '' U) (fun i => measurableSet_iterate_image e hU i.val) hd _
    (fun i => ((measurable_pi_apply i).comp hB).comp (e.symm.measurable.iterate i.val)) _ hp

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] in
lemma paintTower_level (e : X ≃ᵐ X) (U : Set X) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (B : X → (Fin N → A)) (p : X → A) {x : X} (hx : x∈U) (i : Fin N) :
    paintTower e U N B p (e^[i.val] x)=B x i := by
  unfold paintTower
  rw [disjointPaste_on _ hd _ _ (mem_image_of_mem _ hx)]
  rw [(show Function.LeftInverse e.symm (e : X → X) from e.symm_apply_apply).iterate i.val x]

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] in
lemma paintTower_word (e : X ≃ᵐ X) (U : Set X) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (B : X → (Fin N → A)) (p : X → A) {x : X} (hx : x∈U) :
    word e (paintTower e U N B p) N x=B x := by
  funext i
  exact paintTower_level e U N hd B p hx i

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] in
lemma paintTower_off (e : X ≃ᵐ X) (U : Set X) (N : ℕ)
    (B : X → (Fin N → A)) (p : X → A) {x : X}
    (hx : x∉⋃ i : Fin N,(e^[i.val]) '' U) : paintTower e U N B p x=p x :=
  disjointPaste_off _ _ _ hx

lemma measure_iterate_image (μ : Measure X) (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (U : Set X) (i : ℕ) : μ ((e^[i]) '' U)=μ U := by
  have hmp : MeasurePreserving (iterateEquiv e i).symm μ μ :=
    (show MeasurePreserving (iterateEquiv e i) μ μ from by
      simpa only [funext (iterateEquiv_apply e i)] using he.iterate i).symm _
  have hset : (e^[i]) '' U=(iterateEquiv e i).symm ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change (iterateEquiv e i).symm ((iterateEquiv e i) y)∈U
      simpa only [MeasurableEquiv.symm_apply_apply] using hy
    · intro hx
      refine ⟨(iterateEquiv e i).symm x,hx,?_⟩
      exact (iterateEquiv e i).apply_symm_apply x
  rw [hset]
  exact hmp.measure_preimage_equiv U

theorem paintTower_repaint (μ : Measure X) (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {U : Set X} (hU : MeasurableSet U) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    {B : X → (Fin N → A)} (hB : Measurable B) {p : X → A} (hp : Measurable p) :
    μ {x | p x≠paintTower e U N B p x}=
      ∑ i : Fin N,μ (U∩{x | p (e^[i.val] x)≠B x i}) := by
  let S (i : Fin N) : Set X := U∩{x | p (e^[i.val] x)≠B x i}
  have hS (i : Fin N) : MeasurableSet (S i) := hU.inter
    (measurableSet_eq_fun (hp.comp (e.measurable.iterate i.val)) ((measurable_pi_apply i).comp hB)).compl
  have himg (i : Fin N) : (e^[i.val]) '' S i⊆(e^[i.val]) '' U := image_mono inter_subset_left
  have hdisj : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' S i) ((e^[j.val]) '' S j)) :=
    fun i j hij => (hd hij).mono (himg i) (himg j)
  have hset : {x | p x≠paintTower e U N B p x}=⋃ i : Fin N,(e^[i.val]) '' S i := by
    ext x
    constructor
    · intro hx
      have hin : x∈⋃ i : Fin N,(e^[i.val]) '' U := by
        by_contra ho
        exact hx (paintTower_off e U N B p ho).symm
      obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hin
      refine mem_iUnion.mpr ⟨i,y,⟨hy,?_⟩,rfl⟩
      simpa only [mem_ofPred_eq,paintTower_level e U N hd B p hy i] using hx
    · intro hx
      obtain ⟨i,y,⟨hy,hbad⟩,rfl⟩ := mem_iUnion.mp hx
      simpa only [mem_ofPred_eq,paintTower_level e U N hd B p hy i] using hbad
  rw [hset,measure_iUnion hdisj (fun i => measurableSet_iterate_image e (hS i) i.val),tsum_fintype]
  exact Finset.sum_congr rfl (fun i _ => measure_iterate_image μ e he (S i) i.val)

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_ReconstructionEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter HyperbolicCoding
open scoped BigOperators ENNReal Topology
variable {X A B : Type*} [MeasurableSpace X]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (μ : Measure X) [IsProbabilityMeasure μ]

lemma rate_factor (f : X → X) (hf : MeasurePreserving f μ μ)
    (p : X → A) (hp : Measurable p) (g : A → B) :
    rate μ f (g ∘ p) ≤ rate μ f p := by
  have hg : Measurable g := measurable_of_finite g
  apply le_of_tendsto_of_tendsto
    (rate_tendsto μ f hf (g ∘ p) (hg.comp hp)) (rate_tendsto μ f hf p hp)
  apply Eventually.of_forall
  intro n
  have heq : word f (g ∘ p) n = (fun v : Fin n → A => fun i => g (v i)) ∘ word f p n := rfl
  dsimp only
  rw [heq]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact obs_factor μ _ _ (word_measurable f hf.measurable p hp n)
    (word_measurable f hf.measurable (g ∘ p) (hg.comp hp) n)

lemma rate_word_le (f : X → X) (hf : MeasurePreserving f μ μ)
    (p : X → A) (hp : Measurable p) (m : ℕ) :
    rate μ f (word f p m) ≤ rate μ f p := by
  have hb (n : ℕ) : obs μ (word f (word f p m) n) ≤
      obs μ (word f p n) + obs μ (word f p m) := by
    let G : (Fin (n+m) → A) → (Fin n → Fin m → A) :=
      fun v i j => v ⟨i.val+j.val, Nat.add_lt_add i.isLt j.isLt⟩
    have heq : word f (word f p m) n = G ∘ word f p (n+m) := by
      funext x i j
      simp only [word,Function.comp_apply,G,←Function.iterate_add_apply,Nat.add_comm]
    have hh : obs μ (word f (word f p m) n) ≤ obs μ (word f p (n+m)) := by
      rw [heq]
      exact obs_factor μ _ G (word_measurable f hf.measurable p hp (n+m))
        ((measurable_of_finite G).comp (word_measurable f hf.measurable p hp (n+m)))
    exact hh.trans (obs_word_subadd μ f hf p hp n m)
  have hlim : Tendsto (fun n : ℕ => obs μ (word f p n)/(n : ℝ) +
      obs μ (word f p m)/(n : ℝ)) atTop (𝓝 (rate μ f p)) := by
    simpa only [add_zero] using (rate_tendsto μ f hf p hp).add
      (tendsto_const_div_atTop_nhds_zero_nat (obs μ (word f p m)))
  apply le_of_tendsto_of_tendsto
    (rate_tendsto μ f hf (word f p m) (word_measurable f hf.measurable p hp m)) hlim
  apply Eventually.of_forall
  intro n
  simpa only [add_div] using div_le_div_of_nonneg_right (hb n) (Nat.cast_nonneg n)

omit [IsProbabilityMeasure μ] in
lemma rate_integer_shift (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (p : X → A) (hp : Measurable p) (s : ℤ) :
    rate μ e (p ∘ integerIterate e s) = rate μ e p := by
  have hw (n : ℕ) : word e (p ∘ integerIterate e s) n =
      word e p n ∘ integerIterate e s := by
    funext x i
    simp only [word,Function.comp_apply,←integerIterate_nat,
      ←integerIterate_add,add_comm]
  have ho (n : ℕ) : obs μ (word e (p ∘ integerIterate e s) n) = obs μ (word e p n) := by
    rw [hw]
    exact obs_comp_preserving μ _ (integerIterate_measurePreserving e he s)
      _ (word_measurable e e.measurable p hp n)
  unfold rate
  simp only [ho]

lemma rate_le_window_decoder (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (p : X → A) (hp : Measurable p) (q : X → B) (hq : Measurable q)
    (s : ℤ) (m : ℕ) (D : (Fin m → B) → A) :
    rate μ e p ≤ rate μ e q +
      cond μ p (D ∘ word e q m ∘ integerIterate e s) := by
  let r : X → A := D ∘ word e q m ∘ integerIterate e s
  have hr : Measurable r := (measurable_of_finite D).comp
    ((word_measurable e e.measurable q hq m).comp (integerIterate_measurable e s))
  have hR : rate μ e r ≤ rate μ e q := by
    have hshift := rate_integer_shift μ e he (D ∘ word e q m)
      ((measurable_of_finite D).comp (word_measurable e e.measurable q hq m)) s
    change rate μ e ((D ∘ word e q m) ∘ integerIterate e s) ≤ _
    rw [hshift]
    exact (rate_factor μ e he (word e q m) (word_measurable e e.measurable q hq m) D).trans
      (rate_word_le μ e he q hq m)
  exact (rate_comparison μ e he p r hp hr).trans (add_le_add_left hR _)

theorem rate_lower_of_small_window_error (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (p : X → A) (hp : Measurable p) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ,0 < η ∧ ∀ (q : X → B),Measurable q →
      ∀ (s : ℤ) (m : ℕ) (D : (Fin m → B) → A),
      mass μ (errorObs p (D ∘ word e q m ∘ integerIterate e s)) true < η →
      rate μ e p-ε < rate μ e q := by
  obtain ⟨η,hη,hsmall⟩ := cond_small_of_error (α:=A) μ ε hε
  refine ⟨η,hη,?_⟩
  intro q hq s m D hd
  have hr : Measurable (D ∘ word e q m ∘ integerIterate e s) :=
    (measurable_of_finite D).comp
      ((word_measurable e e.measurable q hq m).comp (integerIterate_measurable e s))
  have h1 := rate_le_window_decoder μ e he p hp q hq s m D
  have h2 := hsmall p _ hp hr hd
  linarith

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A C : Type*} [MeasurableSpace X]

lemma word_centered_iterate (e : X ≃ᵐ X) (q : X → A) (n : ℕ)
    (b : X) (i : Fin n) :
    word e q (2*n) (integerIterate e (-(n : ℤ)) (e^[i.val] b)) =
      Marker.centeredWindow n (orbitName e q b) i := by
  funext j
  simp only [word,Marker.centeredWindow,orbitName,←integerIterate_nat,
    ←integerIterate_add]
  congr 2
  omega

theorem marked_tower_decode_symbol (e : X ≃ᵐ X) (p : X → C) (q : X → A)
    {n r : ℕ} (hn : 0 < n) (hr : r < n) (zero one : A) (h01 : zero≠one)
    (D : (Fin n → A) → (Fin n → C)) (b : X) (i : Fin n)
    (hb : Marker.MarkedBlock hr zero one (word e q n b))
    (hD : D (word e q n b) i=p (e^[i.val] b)) :
    Marker.decodeWindow hn hr zero one D
      (word e q (2*n) (integerIterate e (-(n : ℤ)) (e^[i.val] b))) = p (e^[i.val] b) := by
  rw [word_centered_iterate]
  have hw : (fun j : Fin n => orbitName e q b (j.val : ℤ))=word e q n b := by
    funext j
    simp only [orbitName,integerIterate_nat,word]
  rw [Marker.decode_centeredWindow hn hr zero one h01 D _ (by rw [hw]; exact hb),hw]
  exact hD

theorem marked_tower_decode_error_sum (μ : Measure X) (e : X ≃ᵐ X)
    (he : MeasurePreserving e μ μ) (p : X → C) (q : X → A)
    {n r : ℕ} (hn : 0 < n) (hr : r < n) (zero one : A) (h01 : zero≠one)
    (D : (Fin n → A) → (Fin n → C)) (U : Set X) :
    let Bad := fun i : Fin n => U ∩ {b | ¬Marker.MarkedBlock hr zero one (word e q n b) ∨
      D (word e q n b) i≠p (e^[i.val] b)}
    μ {x | Marker.decodeWindow hn hr zero one D
      (word e q (2*n) (integerIterate e (-(n : ℤ)) x))≠p x} ≤
      μ (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ + ∑ i : Fin n,μ (Bad i) := by
  intro Bad
  have hsub : {x | Marker.decodeWindow hn hr zero one D
      (word e q (2*n) (integerIterate e (-(n : ℤ)) x))≠p x} ⊆
      (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ ∪ ⋃ i : Fin n,(e^[i.val]) '' Bad i := by
    intro x hx
    by_cases ht : x∈⋃ i : Fin n,(e^[i.val]) '' U
    · obtain ⟨i,b,hb,rfl⟩ := mem_iUnion.mp ht
      right
      refine mem_iUnion.mpr ⟨i,b,⟨hb,?_⟩,rfl⟩
      by_contra h
      change ¬(¬Marker.MarkedBlock hr zero one (word e q n b) ∨
        D (word e q n b) i≠p (e^[i.val] b)) at h
      push Not at h
      exact hx (marked_tower_decode_symbol e p q hn hr zero one h01 D b i h.1 h.2)
    · exact Or.inl ht
  calc
    _ ≤ μ ((⋃ i : Fin n,(e^[i.val]) '' U)ᶜ ∪ ⋃ i : Fin n,(e^[i.val]) '' Bad i) := measure_mono hsub
    _ ≤ μ (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ + μ (⋃ i : Fin n,(e^[i.val]) '' Bad i) := measure_union_le _ _
    _ ≤ μ (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ + ∑' i : Fin n,μ ((e^[i.val]) '' Bad i) :=
      add_le_add_right (measure_iUnion_le _) _
    _ = _ := by simp only [measure_iterate_image μ e he,tsum_fintype]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A C : Type*} [MeasurableSpace X]

theorem marked_tower_prefix_decoder_error (μ : Measure X) [IsFiniteMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (p : X → C) (q : X → A) {k t r : ℕ} (hn : 0 < k+t) (hr : r < k+t)
    (zero one : A) (h01 : zero≠one)
    (D : (Fin (k+t) → A) → (Fin k → C)) (c₀ : C)
    {U : Set X} (hU : MeasurableSet U)
    (hmarked : ∀ᵐ b ∂μ.restrict U,Marker.MarkedBlock hr zero one (word e q (k+t) b)) :
    μ.real {x | Marker.decodeWindow hn hr zero one (extendPrefixDecoder D c₀)
      (word e q (2*(k+t)) (integerIterate e (-((k+t : ℕ) : ℤ)) x))≠p x} ≤
      μ.real (⋃ i : Fin (k+t),(e^[i.val]) '' U)ᶜ +
      (k+t : ℕ)*μ.real (U∩{b | D (word e q (k+t) b)≠word e p k b})+
      (t : ℝ)*μ.real U := by
  let E := U∩{b | D (word e q (k+t) b)≠word e p k b}
  let Bad := fun i : Fin (k+t) => U∩{b |
    ¬Marker.MarkedBlock hr zero one (word e q (k+t) b) ∨
      extendPrefixDecoder D c₀ (word e q (k+t) b) i≠p (e^[i.val] b)}
  have hmain := marked_tower_decode_error_sum μ e he p q hn hr zero one h01
    (extendPrefixDecoder D c₀) U
  dsimp only at hmain
  have hhead (i : Fin k) : μ (Bad (Fin.castAdd t i)) ≤ μ E := by
    apply measure_mono_ae
    filter_upwards [(ae_restrict_iff' hU).mp hmarked] with b hb
    intro hbad
    refine ⟨hbad.1,?_⟩
    intro hEq
    have hm := hb hbad.1
    have hd := hbad.2.resolve_left (not_not.mpr hm)
    apply hd
    simp only [extendPrefixDecoder,Fin.addCases_left,hEq,word]
    rfl
  have htail (i : Fin t) : μ (Bad (Fin.natAdd k i)) ≤ μ U :=
    measure_mono (inter_subset_left)
  have hsum : (∑ i : Fin (k+t),μ (Bad i))≤(k : ℝ≥0∞)*μ E+(t : ℝ≥0∞)*μ U := by
    rw [Fin.sum_univ_add]
    apply add_le_add
    · simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun i _ => hhead i)
    · simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun i _ => htail i)
  have hEfin : μ E≠⊤ := measure_ne_top _ _
  have hweak : (k : ℝ≥0∞)*μ E≤((k+t : ℕ) : ℝ≥0∞)*μ E :=
    by gcongr; exact_mod_cast Nat.le_add_right k t
  have hbound := hmain.trans (add_le_add_right (hsum.trans (add_le_add_left hweak _)) _)
  have hfin : μ (⋃ i : Fin (k+t),(e^[i.val]) '' U)ᶜ+
      (((k+t : ℕ) : ℝ≥0∞)*μ E+(t : ℝ≥0∞)*μ U)≠⊤ := by finiteness
  have hreal := ENNReal.toReal_mono hfin hbound
  rw [ENNReal.toReal_add (measure_ne_top _ _) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)] at hreal
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, Measure.real, add_assoc, E] using hreal

end HyperbolicCoding

end
section
namespace HyperbolicCoding.MatrixCoupling
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A]
    {p : A → ℝ} {q : B → ℝ}

theorem exists_decodable_coupling_scaled (r : MatrixCoupling p q) (hq : ∑ b,q b=1)
    (c : A → B → ℝ) (hc0 : ∀ a b,0 ≤ c a b) (hc1 : ∀ a b,c a b≤1)
    {τ M : ℝ} (hτ : 0 < τ) (hM : ∀ b,q b≤M) :
    ∃ (D : B → A) (R : MatrixCoupling p q),
      R.cost (fun a b => symbolCost a (D b))≤Real.sqrt ((Fintype.card A : ℝ)*M+τ*r.cost c) ∧
      R.cost c ≤ r.cost c+(Fintype.card A : ℝ)*M/τ+
        Real.sqrt ((Fintype.card A : ℝ)*M+τ*r.cost c) := by
  obtain ⟨D,hD⟩ := r.exists_rounded_decoder hq (fun a b => τ*c a b) hM
  let E : ℝ := ∑ a,|assignedMass q D a-p a|
  let C : ℝ := ∑ b,q b*c (D b) b
  have hE : 0≤E := Finset.sum_nonneg (fun a _ => abs_nonneg _)
  have hC : 0≤C := Finset.sum_nonneg (fun b _ => mul_nonneg (r.right_nonneg b) (hc0 _ _))
  have hsum : (∑ b,q b*(τ*c (D b) b))=τ*C := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hscaledCost : r.cost (fun left right => τ*c left right)=τ*r.cost c := by
    simp only [cost,Finset.mul_sum,mul_left_comm]
  rw [hscaledCost,hsum] at hD
  change E^2+τ*C≤(Fintype.card A : ℝ)*M+τ*r.cost c at hD
  have hnonneg : 0≤(Fintype.card A : ℝ)*M+τ*r.cost c := by
    nlinarith [sq_nonneg E,mul_nonneg hτ.le hC]
  have herror : E≤Real.sqrt ((Fintype.card A : ℝ)*M+τ*r.cost c) := by
    nlinarith [Real.sq_sqrt hnonneg,Real.sqrt_nonneg ((Fintype.card A : ℝ)*M+τ*r.cost c),
      mul_nonneg hτ.le hC]
  have hcost : C ≤ r.cost c+(Fintype.card A : ℝ)*M/τ := by
    have h := (le_div_iff₀ hτ).mpr (show C*τ≤(Fintype.card A : ℝ)*M+τ*r.cost c by
      nlinarith [sq_nonneg E])
    apply h.trans_eq
    field_simp
    ring
  obtain ⟨R,hdecode,hpaint⟩ := r.repair_assignment hq D c hc0 hc1
  refine ⟨D,R,hdecode.trans herror,?_⟩
  change R.cost c≤C+E at hpaint
  linarith

lemma decodingThreshold_pos {ε : ℝ} (hε : 0<ε) : 0<decodingThreshold ε :=
  lt_min (by positivity) (by positivity)

theorem decodable_coupling_tolerance {ε : ℝ} (hε : 0<ε)
    (r : MatrixCoupling p q) (hq : (∑ b,q b)=1)
    (c : A → B → ℝ) (hc0 : ∀ a b,0 ≤ c a b) (hc1 : ∀ a b,c a b≤1)
    (M : ℝ) (hM : ∀ b,q b≤M) (hsmall : (Fintype.card A : ℝ)*M≤decodingThreshold ε) :
    ∃ (D : B → A) (R : MatrixCoupling p q),
      R.cost (fun a b => symbolCost a (D b))<ε ∧ R.cost c < r.cost c+ε := by
  let τ : ℝ := ε^2/16
  have hτ : 0<τ := by dsimp [τ]; positivity
  have hr1 : r.cost c≤1 := by
    calc
      r.cost c ≤ r.cost (fun _ _ => 1) := r.cost_mono _ _ hc1
      _=1 := by
        unfold cost
        simp only [mul_one]
        rw [Finset.sum_comm]
        simp only [r.col,hq]
  obtain ⟨D,R,hD,hR⟩ := r.exists_decodable_coupling_scaled hq c hc0 hc1 hτ hM
  have hs : Real.sqrt ((Fintype.card A : ℝ)*M+τ*r.cost c)<ε/2 := by
    apply (Real.sqrt_lt' (by positivity : 0<ε/2)).mpr
    have h1 : (Fintype.card A : ℝ)*M≤ε^2/16 := hsmall.trans (min_le_left _ _)
    have h2 := mul_le_mul_of_nonneg_left hr1 hτ.le
    dsimp [τ] at h2 ⊢
    nlinarith [sq_pos_of_pos hε]
  have hd : (Fintype.card A : ℝ)*M/τ≤ε/4 := by
    apply (div_le_iff₀ hτ).mpr
    have hb := hsmall.trans (min_le_right _ _)
    change _≤τ*ε/4 at hb
    nlinarith
  exact ⟨D,R,hD.trans_lt (hs.trans (by linarith)),by linarith⟩

end HyperbolicCoding.MatrixCoupling

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_TypicalDecodableCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding.MatrixCoupling
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {p : A → ℝ} {q : B → ℝ}

omit [DecidableEq B] in
lemma sum_extendRows_mul (S : Finset A) (g : S → B → ℝ) (c : A → B → ℝ) :
    (∑ a,∑ b,extendRows S g a b*c a b)=∑ a : S,∑ b,g a b*c a b := by
  have he (a : A) : (∑ b,extendRows S g a b*c a b)=
      if h : a∈S then ∑ b,g ⟨a,h⟩ b*c a b else 0 := by
    unfold extendRows
    split <;> simp_all
  simp_rw [he]
  exact (Finset.sum_attach_eq_sum_dite S (fun a => ∑ b,g a b*c a b)).symm

omit [DecidableEq B] in
lemma replaceSub_cost (R : MatrixCoupling p q) (S : Finset A)
    {u : S → ℝ} {v : B → ℝ} (G H : MatrixCoupling u v)
    (hle : ∀ a b,G.weight a b≤R.weight a b) (c : A → B → ℝ) :
    (R.replaceSub S G H hle).cost c=R.cost c-G.cost (fun a b => c a b)+H.cost (fun a b => c a b) := by
  unfold cost replaceSub
  simp only [add_mul,sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,sum_extendRows_mul]

omit [DecidableEq B] in
lemma replaceSub_bounded_cost (R : MatrixCoupling p q) (hp : ∑ a,p a=1) (S : Finset A)
    {u : S → ℝ} {v : B → ℝ} (G H : MatrixCoupling u v)
    (hle : ∀ a b,G.weight a b≤R.weight a b) (c : A → B → ℝ) (hc1 : ∀ a b,c a b≤1) :
    (R.replaceSub S G H hle).cost c≤1-(∑ a,u a)+H.cost (fun a b => c a b) := by
  have hres (a : A) (b : B) : 0≤R.weight a b-extendRows S G.weight a b := by
    apply sub_nonneg.mpr
    unfold extendRows
    split
    · exact hle _ _
    · exact R.nonneg _ _
  have hb : (∑ a,∑ b,(R.weight a b-extendRows S G.weight a b)*c a b)≤1-(∑ a,u a) := by
    calc
      _≤∑ a,∑ b,(R.weight a b-extendRows S G.weight a b) := by
        apply Finset.sum_le_sum; intro a _
        apply Finset.sum_le_sum; intro b _
        exact mul_le_of_le_one_right (hres a b) (hc1 a b)
      _=_ := by
        simp only [Finset.sum_sub_distrib,R.row,hp]
        congr 1
        rw [Finset.sum_comm]
        simp only [sum_extendRows]
        rw [Finset.sum_comm]
        simp only [G.row]
  rw [replaceSub_cost]
  have he : R.cost c-G.cost (fun a b => c a b)=
      ∑ a,∑ b,(R.weight a b-extendRows S G.weight a b)*c a b := by
    simp only [sub_mul,Finset.sum_sub_distrib,sum_extendRows_mul,cost]
  rw [he]
  linarith

omit [DecidableEq A] [DecidableEq B] in
lemma divide_cost (R : MatrixCoupling p q) {t : ℝ} (ht : 0<t) (c : A → B → ℝ) :
    (R.divide ht).cost c=R.cost c/t := by
  simp only [cost,divide,div_mul_eq_mul_div,←Finset.sum_div]

theorem decodable_coupling_total [Nonempty A] {ε : ℝ} (hε : 0<ε)
    (R : MatrixCoupling p q) (t : ℝ) (ht : 0<t) (hsum : (∑ b,q b)=t)
    (c : A → B → ℝ) (hc0 : ∀ a b,0 ≤ c a b) (hc1 : ∀ a b,c a b≤1)
    (M : ℝ) (hM : ∀ b,q b≤M) (hsmall : (Fintype.card A : ℝ)*M≤t*decodingThreshold ε) :
    ∃ (D : B → A) (H : MatrixCoupling p q),
      H.cost (fun a b => symbolCost a (D b))<t*ε ∧ H.cost c<R.cost c+t*ε := by
  let V := R.divide ht
  have hVs : (∑ b,q b/t)=1 := by rw [←Finset.sum_div,hsum,div_self ht.ne']
  have hVm : ∀ b,q b/t≤M/t := fun b => div_le_div_of_nonneg_right (hM b) ht.le
  have hsize : (Fintype.card A : ℝ)*(M/t)≤decodingThreshold ε := by
    rw [←mul_div_assoc]
    exact (div_le_iff₀ ht).mpr (by simpa only [mul_comm] using hsmall)
  obtain ⟨D,H,hD,hH⟩ := decodable_coupling_tolerance hε V hVs c hc0 hc1 (M/t) hVm hsize
  let W : MatrixCoupling p q := {
    weight a b := t*H.weight a b
    nonneg a b := mul_nonneg ht.le (H.nonneg a b)
    row a := by rw [←Finset.mul_sum,H.row]; exact mul_div_cancel₀ _ ht.ne'
    col b := by rw [←Finset.mul_sum,H.col]; exact mul_div_cancel₀ _ ht.ne' }
  have hwcost (d : A → B → ℝ) : W.cost d=t*H.cost d := by
    unfold cost
    simp only [W,mul_assoc,←Finset.mul_sum]
  refine ⟨D,W,?_,?_⟩
  · rw [hwcost]
    exact mul_lt_mul_of_pos_left hD ht
  · rw [hwcost]
    have h := mul_lt_mul_of_pos_left hH ht
    rw [show V.cost c=R.cost c/t from R.divide_cost ht c] at h
    rw [mul_add,mul_div_cancel₀ _ ht.ne'] at h
    exact h

theorem decodable_subtransport {ε : ℝ} (hε : 0<ε)
    (R : MatrixCoupling p q) (hp : ∑ a,p a=1) (S : Finset A) (hS : S.Nonempty)
    {u : S → ℝ} {v : B → ℝ} (G : MatrixCoupling u v)
    (hle : ∀ a b,G.weight a b≤R.weight a b) (t : ℝ) (ht : 0<t) (hsum : (∑ a,u a)=t)
    (c : A → B → ℝ) (hc0 : ∀ a b,0 ≤ c a b) (hc1 : ∀ a b,c a b≤1)
    (M : ℝ) (hM : ∀ b,v b≤M) (hsmall : (S.card : ℝ)*M≤t*decodingThreshold ε) :
    ∃ (D : B → A) (H : MatrixCoupling p q),
      H.cost (fun a b => symbolCost a (D b))<1-t+t*ε ∧ H.cost c<R.cost c+t*ε := by
  obtain ⟨a,ha⟩ := hS
  have : Nonempty S := ⟨⟨a,ha⟩⟩
  have hsumv : (∑ b,v b)=t := by
    simp_rw [←G.col]
    rw [Finset.sum_comm]
    simp only [G.row,hsum]
  obtain ⟨D,H,hD,hH⟩ := decodable_coupling_total hε G t ht hsumv
    (fun a b => c a b) (fun a b => hc0 a b) (fun a b => hc1 a b) M hM (by simpa using hsmall)
  let D' : B → A := fun b => (D b).val
  let H' := R.replaceSub S G H hle
  have he (a : S) (b : B) : symbolCost (a : A) (D' b)=symbolCost a (D b) := by
    simp only [symbolCost,D',Subtype.val_inj]
    split_ifs <;> rfl
  have hb := R.replaceSub_bounded_cost hp S G H hle (fun a b => symbolCost a (D' b))
    (fun a b => symbolCost_le_one a (D' b))
  simp_rw [he] at hb
  rw [hsum] at hb
  refine ⟨D',H',by dsimp only [H']; linarith,?_⟩
  dsimp only [H']
  rw [replaceSub_cost]
  linarith

omit [DecidableEq A] in
lemma rectangle_weight_le (R : MatrixCoupling p q) (S : Finset A) (T : Finset B) (a : S) (b : B) :
    (R.rectangle S T).weight a b≤R.weight a b := by
  dsimp [rectangle]
  split
  · exact le_rfl
  · exact R.nonneg _ _

omit [DecidableEq B] in
lemma sum_subtype_weight_le (R : MatrixCoupling p q) (S : Finset A) (b : B) :
    (∑ a : S,R.weight a b)≤q b := by
  rw [←sum_extendRows S (fun a b => R.weight a b) b,←R.col b]
  apply Finset.sum_le_sum
  intro a _
  unfold extendRows
  split
  · exact le_rfl
  · exact R.nonneg _ _

lemma rectangle_right_bound (R : MatrixCoupling p q) (S : Finset A) (T : Finset B)
    {M : ℝ} (hM0 : 0≤M) (hM : ∀ b∈T,q b≤M) (b : B) :
    (∑ a : S,if b∈T then R.weight a b else 0)≤M := by
  by_cases hb : b∈T
  · simpa only [ite_eq_left hb] using (R.sum_subtype_weight_le S b).trans (hM b hb)
  · simpa only [ite_eq_right hb,Finset.sum_const_zero] using hM0

omit [DecidableEq A] in
lemma rectangle_mass (R : MatrixCoupling p q) (S : Finset A) (T : Finset B) :
    (∑ a : S,∑ b,if b∈T then R.weight a b else 0)=∑ a∈S,∑ b∈T,R.weight a b := by
  simp only [Finset.sum_ite_mem,Finset.univ_inter]
  exact (Finset.sum_subtype S (fun _ => Iff.rfl) (fun a : A => ∑ b∈T,R.weight a b)).symm

omit [DecidableEq A] in
lemma rectangle_mass_ge (R : MatrixCoupling p q) (hp : ∑ a,p a=1) (S : Finset A) (T : Finset B) :
    (∑ a∈S,p a)+(∑ b∈T,q b)-1≤∑ a : S,∑ b,if b∈T then R.weight a b else 0 := by
  rw [rectangle_mass]
  have hsplit : (∑ a∈S,p a)=(∑ a∈S,∑ b∈T,R.weight a b)+(∑ a∈S,∑ b∈Tᶜ,R.weight a b) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_add_sum_compl,R.row]
  have hbad : (∑ a∈S,∑ b∈Tᶜ,R.weight a b)≤∑ b∈Tᶜ,q b := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro b _
    rw [←R.col b]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun a _ _ => R.nonneg a b)
  have htotal : (∑ b∈T,q b)+(∑ b∈Tᶜ,q b)=1 := by
    rw [Finset.sum_add_sum_compl]
    simp_rw [←R.col]
    rw [Finset.sum_comm]
    simp only [R.row,hp]
  linarith

theorem decodable_typical_coupling {ε θ : ℝ} (hε : 0 < ε)
    (_hθ : 0 ≤ θ) (hθsmall : θ < 1/2)
    (R : MatrixCoupling p q) (hp : ∑ a,p a=1)
    (S : Finset A) (T : Finset B)
    (hS : 1-θ ≤ ∑ a∈S,p a) (hT : 1-θ ≤ ∑ b∈T,q b)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ b∈T,q b ≤ M)
    (hsize : (S.card : ℝ)*M ≤ (1-2*θ)*decodingThreshold ε)
    (c : A → B → ℝ) (hc0 : ∀ a b,0 ≤ c a b) (hc1 : ∀ a b,c a b ≤ 1) :
    ∃ (D : B → A) (H : MatrixCoupling p q),
      H.cost (fun a b => symbolCost a (D b)) < 2*θ+ε ∧ H.cost c < R.cost c+ε := by
  let G := R.rectangle S T
  let t : ℝ := ∑ a : S,∑ b,if b∈T then R.weight a b else 0
  have htlo : 1-2*θ ≤ t := by
    have h := R.rectangle_mass_ge hp S T
    dsimp only [t]
    linarith
  have ht : 0 < t := by linarith
  have hthi : t ≤ 1 := by
    dsimp only [t]
    rw [R.rectangle_mass]
    calc
      _ ≤ ∑ a∈S,∑ b,R.weight a b := by
        apply Finset.sum_le_sum
        intro a _
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
          (fun b _ _ => R.nonneg a b)
      _ = ∑ a∈S,p a := by simp only [R.row]
      _ ≤ ∑ a,p a := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun a _ _ => R.left_nonneg a)
      _ = 1 := hp
  have hSne : S.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he,Finset.sum_empty] at hS
    linarith
  have hthreshold : 0 ≤ decodingThreshold ε := (decodingThreshold_pos hε).le
  have hsize' : (S.card : ℝ)*M ≤ t*decodingThreshold ε :=
    hsize.trans (mul_le_mul_of_nonneg_right htlo hthreshold)
  obtain ⟨D,H,hD,hH⟩ := decodable_subtransport hε R hp S hSne G
    (R.rectangle_weight_le S T) t ht rfl c hc0 hc1 M
    (R.rectangle_right_bound S T hM0 hM) hsize'
  have hte : t*ε ≤ ε := mul_le_of_le_one_left hε.le hthi
  exact ⟨D,H,by linarith,by linarith⟩

end HyperbolicCoding.MatrixCoupling

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

omit [Fintype B] in
lemma pushWeight_add (q r : A → ℝ) (f : A → B) (b : B) :
    pushWeight (fun a => q a+r a) f b=pushWeight q f b+pushWeight r f b := by
  simp only [pushWeight,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split <;> simp

omit [Fintype B] in
lemma pushWeight_bound (q : A → ℝ) (f : A → B) {M K : ℝ} (hM : ∀ a,q a ≤ M)
    (hM0 : 0 ≤ M) (hf : ∀ b,(Fintype.card {a // f a=b} : ℝ) ≤ K) (b : B) :
    pushWeight q f b ≤ K*M := by
  calc
    _ ≤ ∑ a : A,if f a=b then M else 0 := by
      apply Finset.sum_le_sum
      intro a _
      split <;> first | exact hM a | exact le_rfl
    _ = (Fintype.card {a // f a=b} : ℝ)*M := by
      simp only [Finset.sum_ite,Finset.sum_const,nsmul_eq_mul,mul_zero,add_zero]
      congr 1
      rw [Fintype.card_subtype]
    _ ≤ K*M := mul_le_mul_of_nonneg_right (hf b) hM0

theorem typical_pushforward [DecidableEq A]
    (q : A → ℝ) (hq : ∀ a,0 ≤ q a) (hs : ∑ a,q a=1)
    (f : A → B) (S : Finset A) {M K ε : ℝ} (hM0 : 0 ≤ M) (_hK0 : 0 ≤ K)
    (hM : ∀ a∈S,q a ≤ M) (hf : ∀ b,(Fintype.card {a // f a=b} : ℝ) ≤ K)
    (hbad : (∑ a : A,if a∉S then q a else 0) ≤ ε) :
    ∃ T : Finset B,
      (∀ b∈T,pushWeight q f b ≤ 2*K*M) ∧
      1-2*ε ≤ ∑ b∈T,pushWeight q f b := by
  let u : A → ℝ := fun a => if a∈S then q a else 0
  let v : A → ℝ := fun a => if a∉S then q a else 0
  have hu0 : ∀ a,0 ≤ u a := by intro a; dsimp [u]; split <;> first | exact hq a | exact le_rfl
  have hv0 : ∀ a,0 ≤ v a := by intro a; dsimp [v]; split <;> first | exact hq a | exact le_rfl
  have huM : ∀ a,u a ≤ M := by
    intro a; dsimp [u]; split
    · exact hM a ‹_›
    · exact hM0
  have heq (a : A) : q a=u a+v a := by
    dsimp [u,v]
    by_cases ha : a∈S <;> simp [ha]
  have hpush (b : B) : pushWeight q f b=pushWeight u f b+pushWeight v f b := by
    conv_lhs => rw [show q=(fun a => u a+v a) from funext heq]
    exact pushWeight_add u v f b
  have hub (b : B) : pushWeight u f b ≤ K*M := pushWeight_bound u f huM hM0 hf b
  let T := Finset.univ.filter (fun b => pushWeight v f b ≤ K*M)
  have hmem (b : B) : b∈T ↔ pushWeight v f b ≤ K*M := by simp [T]
  refine ⟨T,?_,?_⟩
  · intro b hb
    rw [hmem] at hb
    rw [hpush]
    linarith [hub b]
  · have hout : (∑ b∈Tᶜ,pushWeight q f b) ≤ 2*ε := by
      calc
        _ ≤ ∑ b∈Tᶜ,2*pushWeight v f b := by
          apply Finset.sum_le_sum
          intro b hb
          have hnot : K*M < pushWeight v f b := by
            have := Finset.mem_compl.mp hb
            rw [hmem] at this
            exact lt_of_not_ge this
          rw [hpush]
          linarith [hub b]
        _ = 2*(∑ b∈Tᶜ,pushWeight v f b) := by rw [Finset.mul_sum]
        _ ≤ 2*(∑ b,pushWeight v f b) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun b _ _ => pushWeight_nonneg v hv0 f b)
        _ ≤ 2*ε := by rw [pushWeight_sum]; exact mul_le_mul_of_nonneg_left hbad (by norm_num)
    have hsplit : (∑ b∈T,pushWeight q f b)+(∑ b∈Tᶜ,pushWeight q f b)=1 := by
      rw [Finset.sum_add_sum_compl,pushWeight_sum,hs]
    linarith

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ}

lemma pushRight_cost [DecidableEq C] (R : MatrixCoupling p q) (f : B → C) (c : A → C → ℝ) :
    (R.pushRight f).cost c=R.cost (fun a b => c a (f b)) := by
  simp only [cost,pushRight,pushWeight,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

end MatrixCoupling

omit [Fintype A] in
lemma mass_mem_finset {X : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → A) (hp : Measurable p) (S : Finset A) :
    (∑ a∈S,mass μ p a)=μ.real {x | p x∈S} := by
  have hm (a : A) : mass μ p a=(μ.map p).real {a} :=
    (map_measureReal_apply hp (measurableSet_singleton a)).symm
  simp_rw [hm]
  rw [sum_measureReal_singleton,map_measureReal_apply hp S.measurableSet]
  rfl

omit [Fintype A] in
lemma mass_codebook_lower {X : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (hp : Measurable p) (S : Finset A) {ε : ℝ}
    (hbad : μ.real {x | p x∉S}<ε) : 1-ε < ∑ a∈S,mass μ p a := by
  rw [mass_mem_finset μ p hp S]
  have hh := measureReal_add_measureReal_compl (μ:=μ) (hp S.measurableSet)
  have he : (p ⁻¹' (S : Set A))ᶜ={x | p x∉S} := rfl
  rw [he] at hh
  simp only [Measure.real,measure_univ,ENNReal.toReal_one] at hh
  change μ.real {x | p x∈S}+μ.real {x | p x∉S}=1 at hh
  linarith

end HyperbolicCoding

end
section
namespace HyperbolicCoding.MatrixCoupling
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {p : A → ℝ} {q : B → ℝ}

theorem decodable_after_sanitizing {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 ≤ θ)
    (hθsmall : θ < 1/4) (R : MatrixCoupling p q) (hp : ∑ a,p a=1)
    (S : Finset A) (T : Finset B) (hS : 1-θ ≤ ∑ a∈S,p a)
    (hbad : (∑ b : B,if b∉T then q b else 0) ≤ θ)
    (f : B → B) (M K : ℝ) (hM0 : 0 ≤ M) (hK0 : 0 ≤ K)
    (hM : ∀ b∈T,q b ≤ M) (hf : ∀ b,(Fintype.card {v // f v=b} : ℝ) ≤ K)
    (hsize : (S.card : ℝ)*(2*K*M) ≤ (1-4*θ)*decodingThreshold ε)
    (c : A → B → ℝ) (hc0 : ∀ a b,0 ≤ c a b) (hc1 : ∀ a b,c a b ≤ 1)
    (κ : ℝ) (hcmap : ∀ a b,c a (f b) ≤ c a b+κ) :
    ∃ (D : B → A) (H : MatrixCoupling p (pushWeight q f)),
      H.cost (fun a b => symbolCost a (D b)) < 4*θ+ε ∧
      H.cost c < R.cost c+κ+ε := by
  have hq : (∑ b,q b)=1 := by
    simp_rw [←R.col]
    rw [Finset.sum_comm]
    simp only [R.row,hp]
  obtain ⟨V,hVm,hV⟩ := typical_pushforward q R.right_nonneg hq f T hM0 hK0 hM hf hbad
  have hs2 : 1-2*θ ≤ ∑ a∈S,p a := by linarith
  have hsize' : (S.card : ℝ)*(2*K*M) ≤ (1-2*(2*θ))*decodingThreshold ε := by
    convert hsize using 1
    all_goals try with_reducible_and_instances rfl
    ring
  obtain ⟨D,H,hD,hH⟩ := decodable_typical_coupling hε (show 0 ≤ 2*θ by positivity)
    (show 2*θ < 1/2 by linarith) (R.pushRight f) hp S V hs2 hV (2*K*M)
    (by positivity) hVm hsize' c hc0 hc1
  have hcost : (R.pushRight f).cost c ≤ R.cost c+κ := by
    rw [pushRight_cost]
    have h := R.cost_mono (fun a b => c a (f b)) (fun a b => 1*c a b+κ)
      (fun a b => by simpa only [one_mul] using hcmap a b)
    rw [R.cost_affine hp 1 κ c,one_mul] at h
    exact h
  refine ⟨D,H,?_,?_⟩ <;> linarith

theorem marked_word_decodable_coupling {C : Type*} [Fintype C] [DecidableEq C]
    {n r : ℕ} {u : C → ℝ} (β : A → ℝ) (_hβ : ∀ a,0 ≤ β a) (_hβsum : ∑ a,β a=1)
    {ε θ L : ℝ} (hε : 0 < ε) (hθ : 0 ≤ θ) (hθsmall : θ < 1/4)
    (R : MatrixCoupling u (productWordWeight β n)) (hu : ∑ a,u a=1)
    (S : Finset C) (T : Finset (Fin n → A)) (hS : 1-θ ≤ ∑ a∈S,u a)
    (hT : ∀ w∈T,productWordWeight β n w ≤ Real.exp (-L))
    (hbad : (∑ w : Fin n → A,if w∉T then productWordWeight β n w else 0) ≤ θ)
    (zero one : A)
    (hsize : (S.card : ℝ)*(2*(Fintype.card A : ℝ)^(Marker.reserved n r).card*Real.exp (-L)) ≤
      (1-4*θ)*decodingThreshold ε)
    (c : C → (Fin n → A) → ℝ) (hc0 : ∀ a b,0 ≤ c a b) (hc1 : ∀ a b,c a b ≤ 1)
    (κ : ℝ) (hcmap : ∀ a b,c a (Marker.markWord r zero one b) ≤ c a b+κ) :
    ∃ (D : (Fin n → A) → C)
      (H : MatrixCoupling u (pushWeight (productWordWeight β n) (Marker.markWord r zero one))),
      H.cost (fun a b => symbolCost a (D b)) < 4*θ+ε ∧
      H.cost c < R.cost c+κ+ε := by
  apply decodable_after_sanitizing hε hθ hθsmall R hu S T hS hbad
    (Marker.markWord r zero one) (Real.exp (-L)) ((Fintype.card A : ℝ)^(Marker.reserved n r).card)
    (Real.exp_pos _).le (by positivity) hT _ hsize c hc0 hc1 κ hcmap
  intro b
  exact_mod_cast Marker.markWord_fiber_card (r:=r) zero one b

end HyperbolicCoding.MatrixCoupling

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Towers_PhaseAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {X A B I : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B] [Fintype I]

omit [StandardBorelSpace X] [Fintype A] [MeasurableSingletonClass A] in
lemma map_restrict_image_equiv (μ : Measure X) (f : X ≃ᵐ X) (hf : MeasurePreserving f μ μ)
    (U : Set X) (p : X → A) (hp : Measurable p) :
    (μ.restrict (f '' U)).map p=(μ.restrict U).map (p ∘ f) := by
  have hh := hf.restrict_image_emb f.measurableEmbedding U
  rw [←hh.map_eq,Measure.map_map hp f.measurable]

omit [StandardBorelSpace X] [Fintype A] [MeasurableSingletonClass A] in
lemma map_restrict_finite_iUnion (μ : Measure X) (S : I → Set X)
    (hS : ∀ i,MeasurableSet (S i)) (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (p : X → A) (hp : Measurable p) :
    (μ.restrict (⋃ i,S i)).map p=∑ i,(μ.restrict (S i)).map p := by
  rw [Measure.restrict_iUnion hd hS,Measure.map_sum hp.aemeasurable,Measure.sum_fintype]

theorem exists_phase_averaging (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (f : I → X ≃ᵐ X) (hf : ∀ i,MeasurePreserving (f i) μ μ)
    {U : Set X} (hU : MeasurableSet U)
    (hd : Pairwise (fun i j => Disjoint (f i '' U) (f j '' U)))
    (p : X → A) (hp : Measurable p) :
    ∃ q : X → B,Measurable q ∧ ∀ c : I → B,
      (μ.restrict (⋃ i,f i '' (U∩q ⁻¹' {c i}))).map p=
        (Fintype.card B : ℝ≥0∞)⁻¹ • (μ.restrict (⋃ i,f i '' U)).map p := by
  classical
  let P : X → (I → A) := fun x i => p (f i x)
  have hP : Measurable P := Measurable.of_eval (fun i => hp.comp (f i).measurable)
  obtain ⟨q,hq,hphase⟩ := exists_independent_finite_phase (B:=B) (μ.restrict U) P hP
  refine ⟨q,hq,fun c => ?_⟩
  have hS (i : I) : MeasurableSet (f i '' (U∩q ⁻¹' {c i})) :=
    (f i).measurableSet_image.mpr (hU.inter (hq (measurableSet_singleton _)))
  have hS0 (i : I) : MeasurableSet (f i '' U) := (f i).measurableSet_image.mpr hU
  have hd' : Pairwise (fun i j => Disjoint (f i '' (U∩q ⁻¹' {c i})) (f j '' (U∩q ⁻¹' {c j}))) :=
    fun i j hij => (hd hij).mono (image_mono inter_subset_left) (image_mono inter_subset_left)
  rw [map_restrict_finite_iUnion μ _ hS hd' p hp,map_restrict_finite_iUnion μ _ hS0 hd p hp,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_restrict_image_equiv μ (f i) (hf i) _ p hp,map_restrict_image_equiv μ (f i) (hf i) U p hp]
  have hh := finite_phase_factor (μ.restrict U) P hP q (c i) (hphase (c i))
    (fun w : I → A => w i) (measurable_pi_apply i)
  rw [Measure.restrict_restrict (hq (measurableSet_singleton _)),inter_comm] at hh
  exact hh

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {X : Type*} [MeasurableSpace X]

lemma phaseBlockStart_add_lt (n K : ℕ) (kr : Fin K × Fin n) (i : Fin n) :
    i.val+phaseBlockStart n kr<(K+2)*n := by
  have hk := Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr kr.1.isLt)
  have hr := kr.2.isLt
  have hi := i.isLt
  simp only [phaseBlockStart,Nat.add_mul,Nat.one_mul,Nat.succ_eq_add_one] at hk ⊢
  omega

lemma phaseBlockStart_lt (n K : ℕ) (kr : Fin K × Fin n) : phaseBlockStart n kr<(K+2)*n := by
  have hn : 0<n := Nat.zero_lt_of_lt kr.2.isLt
  exact (Nat.le_add_left _ 0).trans_lt (phaseBlockStart_add_lt n K kr ⟨0,hn⟩)

lemma phaseBlockStart_injective {n K : ℕ} (hn : 0<n) :
    Function.Injective (phaseBlockStart n (K:=K)) := by
  rintro ⟨k,r⟩ ⟨k',r'⟩ he
  have hh : k.val*n+r.val=k'.val*n+r'.val := by simpa only [phaseBlockStart,Nat.add_assoc,Nat.add_right_inj] using he
  have hr : r.val=r'.val := by
    have hm := congrArg (fun t => t%n) hh
    simpa only [Nat.mul_add_mod_self_right,
      Nat.mod_eq_of_lt r.isLt,Nat.mod_eq_of_lt r'.isLt] using hm
  have hk : k.val=k'.val := Nat.eq_of_mul_eq_mul_right hn (by omega)
  exact Prod.ext (Fin.ext hk) (Fin.ext hr)

lemma measurableSet_phaseBlockBase (e : X ≃ᵐ X) {U : Set X} (hU : MeasurableSet U)
    (n K : ℕ) {q : X → Fin n} (hq : Measurable q) : MeasurableSet (phaseBlockBase e U n K q) :=
  MeasurableSet.iUnion (fun kr => measurableSet_iterate_image e
    (hU.inter (hq (measurableSet_singleton _))) (phaseBlockStart n kr))

lemma phaseBlockBase_level (e : X ≃ᵐ X) (U : Set X) (n K : ℕ) (q : X → Fin n) (i : ℕ) :
    (e^[i]) '' phaseBlockBase e U n K q=
      ⋃ kr : Fin K × Fin n,(e^[i+phaseBlockStart n kr]) '' (U∩q ⁻¹' {kr.2}) := by
  rw [phaseBlockBase,image_iUnion]
  apply iUnion_congr
  intro kr
  rw [image_image]
  congr 1
  exact (Function.iterate_add e i (phaseBlockStart n kr)).symm

lemma phaseBlockBase_disjoint (e : X ≃ᵐ X) (U : Set X) {n K : ℕ} (_ : 0<n)
    (hd : Pairwise (fun i j : Fin ((K+2)*n) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (q : X → Fin n) : Pairwise (fun i j : Fin n =>
      Disjoint ((e^[i.val]) '' phaseBlockBase e U n K q) ((e^[j.val]) '' phaseBlockBase e U n K q)) := by
  intro i j hij
  rw [phaseBlockBase_level,phaseBlockBase_level]
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨kr,y,hy,hyi⟩ := mem_iUnion.mp hxi
  obtain ⟨lr,z,hz,hzj⟩ := mem_iUnion.mp hxj
  let a : Fin ((K+2)*n) := ⟨i.val+phaseBlockStart n kr,phaseBlockStart_add_lt n K kr i⟩
  let b : Fin ((K+2)*n) := ⟨j.val+phaseBlockStart n lr,phaseBlockStart_add_lt n K lr j⟩
  have hab : a=b := by
    by_contra hne
    exact Set.disjoint_left.mp (hd hne) (show x∈(e^[a.val]) '' U from ⟨y,hy.1,hyi⟩)
      (show x∈(e^[b.val]) '' U from ⟨z,hz.1,hzj⟩)
  have he : i.val+phaseBlockStart n kr=j.val+phaseBlockStart n lr := congrArg Fin.val hab
  have hyz : y=z := (e.injective.iterate (i.val+phaseBlockStart n kr))
    (hyi.trans (by simpa only [he] using hzj.symm))
  have hr : kr.2=lr.2 := hy.2.symm.trans (hyz ▸ hz.2)
  have hnum : kr.1.val*n+i.val=lr.1.val*n+j.val := by
    simp only [phaseBlockStart,hr] at he
    omega
  have hi : i.val=j.val := by
    have hm := congrArg (fun t => t%n) hnum
    simpa only [Nat.mul_add_mod_self_right,
      Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using hm
  exact hij (Fin.ext hi)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [StandardBorelSpace X] in
lemma measurableSet_middleTower (e : X ≃ᵐ X) {U : Set X} (hU : MeasurableSet U) (n K : ℕ) :
    MeasurableSet (middleTower e U n K) :=
  MeasurableSet.iUnion (fun _ => measurableSet_iterate_image e hU _)

omit [StandardBorelSpace X] in
lemma middleTower_disjoint (e : X ≃ᵐ X) (U : Set X) {n K : ℕ} (hn : 0<n)
    (hd : Pairwise (fun i j : Fin ((K+2)*n) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U))) :
    Pairwise (fun kr lr : Fin K × Fin n =>
      Disjoint ((e^[phaseBlockStart n kr]) '' U) ((e^[phaseBlockStart n lr]) '' U)) := by
  intro kr lr hne
  exact hd (i:=⟨phaseBlockStart n kr,phaseBlockStart_lt n K kr⟩)
    (j:=⟨phaseBlockStart n lr,phaseBlockStart_lt n K lr⟩) (fun hh =>
      hne (phaseBlockStart_injective hn (congrArg Fin.val hh)))

omit [StandardBorelSpace X] in
lemma middleTower_measure (μ : Measure X) (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {U : Set X} (hU : MeasurableSet U) {n K : ℕ} (hn : 0<n)
    (hd : Pairwise (fun i j : Fin ((K+2)*n) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U))) :
    μ (middleTower e U n K)=(K*n : ℕ)*μ U := by
  rw [middleTower,measure_iUnion (middleTower_disjoint e U hn hd)
    (fun _ => measurableSet_iterate_image e hU _),tsum_fintype]
  simp only [measure_iterate_image μ e he,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
    Fintype.card_fin,nsmul_eq_mul]

theorem exists_unbiased_block_base (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {U : Set X} (hU : MeasurableSet U) {n K : ℕ} (hn : 0<n)
    (hd : Pairwise (fun i j : Fin ((K+2)*n) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (p : X → A) (hp : Measurable p) :
    ∃ V : Set X,MeasurableSet V ∧
      Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' V) ((e^[j.val]) '' V)) ∧
      (μ.restrict V).map p=(n : ℝ≥0∞)⁻¹ • (μ.restrict (middleTower e U n K)).map p ∧
      μ V=(K : ℝ≥0∞)*μ U := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let f (kr : Fin K × Fin n) : X ≃ᵐ X := iterateEquiv e (phaseBlockStart n kr)
  have hf (kr : Fin K × Fin n) : MeasurePreserving (f kr) μ μ :=
    iterateEquiv_measurePreserving e he _
  have hdf : Pairwise (fun kr lr => Disjoint (f kr '' U) (f lr '' U)) := by
    intro kr lr hne
    simpa only [f,funext (iterateEquiv_apply e (phaseBlockStart n kr)),
      funext (iterateEquiv_apply e (phaseBlockStart n lr))] using middleTower_disjoint e U hn hd hne
  obtain ⟨q,hq,hphase⟩ := exists_phase_averaging (B:=Fin n) μ f hf hU hdf p hp
  let V := phaseBlockBase e U n K q
  have hmap : (μ.restrict V).map p=(n : ℝ≥0∞)⁻¹ • (μ.restrict (middleTower e U n K)).map p := by
    have hh := hphase (fun kr => kr.2)
    have hfcoe (kr : Fin K×Fin n) : (f kr : X → X)=e^[phaseBlockStart n kr] :=
      funext (iterateEquiv_apply e _)
    simpa only [hfcoe,Fintype.card_fin,V,phaseBlockBase,middleTower] using hh
  refine ⟨V,measurableSet_phaseBlockBase e hU n K hq,phaseBlockBase_disjoint e U hn hd q,hmap,?_⟩
  have hm := congrArg (fun M : Measure A => M univ) hmap
  simp only [Measure.map_apply hp MeasurableSet.univ,preimage_univ,Measure.restrict_apply_univ,
    Measure.smul_apply,smul_eq_mul] at hm
  rw [middleTower_measure μ e he hU hn hd] at hm
  have hn0 : (n : ℝ≥0∞)≠0 := by exact_mod_cast hn.ne'
  have hnf : (n : ℝ≥0∞)≠⊤ := by simp
  rw [hm,Nat.cast_mul]
  calc
    (n : ℝ≥0∞)⁻¹*((K : ℝ≥0∞)*n*μ U)=(K : ℝ≥0∞)*((n : ℝ≥0∞)⁻¹*n)*μ U := by ring
    _=(K : ℝ≥0∞)*μ U := by rw [ENNReal.inv_mul_cancel hn0 hnf,mul_one]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

theorem normalized_restriction_lawClose (μ : Measure X) [IsProbabilityMeasure μ]
    {U : Set X} (hU : MeasurableSet U) (hUp : 0<μ U) :
    LawClose ((μ U)⁻¹ • μ.restrict U) μ (1-μ.real U) := by
  have hb0 : 0<μ.real U := ENNReal.toReal_pos hUp.ne' (measure_ne_top _ _)
  have hb1 : μ.real U≤1 := by
    have hh := measureReal_mono (μ:=μ) (subset_univ U)
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using hh
  intro S hS
  have hnorm : (((μ U)⁻¹ • μ.restrict U).real S)=μ.real (S∩U)/μ.real U := by
    rw [Measure.real,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv,
      Measure.restrict_apply hS]
    exact (div_eq_inv_mul _ _).symm
  rw [hnorm,abs_le]
  have hc0 : 0≤μ.real (S∩U) := ENNReal.toReal_nonneg
  have hcS : μ.real (S∩U)≤μ.real S := measureReal_mono inter_subset_left
  have hcU : μ.real (S∩U)≤μ.real U := measureReal_mono inter_subset_right
  have hcomp : μ.real U+μ.real Uᶜ=1 := by
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using
      measureReal_add_measureReal_compl (μ:=μ) hU
  have hSc : μ.real S≤μ.real (S∩U)+(1-μ.real U) := by
    have hsub : S⊆(S∩U)∪Uᶜ := by
      intro x hx
      by_cases hxU : x∈U
      · exact Or.inl ⟨hx,hxU⟩
      · exact Or.inr hxU
    have hh := (measureReal_mono (μ:=μ) hsub).trans (measureReal_union_le (μ:=μ) (S∩U) Uᶜ)
    linarith
  constructor
  · have hh : (-(1-μ.real U)+μ.real S)*μ.real U≤μ.real (S∩U) := by
      nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hb1)]
    have hh' := (le_div_iff₀ hb0).mpr hh
    linarith
  · have hh : μ.real (S∩U)≤(1-μ.real U+μ.real S)*μ.real U := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hcU) (sub_nonneg.mpr hb1)]
    have hh' := (div_le_iff₀ hb0).mpr hh
    linarith

lemma normalized_restriction_observation_close (μ : Measure X) [IsProbabilityMeasure μ]
    {U : Set X} (hU : MeasurableSet U) (hUp : 0<μ U)
    (p : X → A) (hp : Measurable p) :
    LawClose (((μ U)⁻¹ • μ.restrict U).map p) (μ.map p) (1-μ.real U) :=
  (normalized_restriction_lawClose μ hU hUp).map hp

lemma normalize_scaled_observation (ν ρ : Measure X) (p : X → A) (hp : Measurable p)
    {c : ℝ≥0∞} (hc0 : c≠0) (hcf : c≠⊤) (h : ν.map p=c • ρ.map p) :
    (((ν univ)⁻¹ • ν).map p)=(((ρ univ)⁻¹ • ρ).map p) := by
  have hm := congrArg (fun M : Measure A => M univ) h
  simp only [Measure.map_apply hp MeasurableSet.univ,preimage_univ,
    Measure.smul_apply,smul_eq_mul] at hm
  rw [Measure.map_smul,Measure.map_smul,h,smul_smul,hm]
  have hs : (c*ρ univ)⁻¹*c=(ρ univ)⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hcf)]
    calc
      c⁻¹*(ρ univ)⁻¹*c=(ρ univ)⁻¹*(c⁻¹*c) := by ring
      _=(ρ univ)⁻¹ := by rw [ENNReal.inv_mul_cancel hc0 hcf,mul_one]
  rw [hs]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [StandardBorelSpace X] in
lemma tower_measure (μ : Measure X) (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {U : Set X} (hU : MeasurableSet U) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U))) :
    μ (⋃ i : Fin N,(e^[i.val]) '' U)=(N : ℝ≥0∞)*μ U := by
  rw [measure_iUnion hd (fun i => measurableSet_iterate_image e hU i.val),tsum_fintype]
  simp only [measure_iterate_image μ e he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem exists_unbiased_rohlin_tower [TopologicalSpace X] [SecondCountableTopology X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    {n : ℕ} (hn : 0<n) (p : X → A) (hp : Measurable p) {ε : ℝ} (hε : 0<ε) :
    ∃ V : Set X,MeasurableSet V ∧ 0<μ V ∧
      Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' V) ((e^[j.val]) '' V)) ∧
      μ.real (⋃ i : Fin n,(e^[i.val]) '' V)ᶜ<ε ∧
      LawClose (((μ V)⁻¹ • μ.restrict V).map p) (μ.map p) ε := by
  let δ : ℝ := min (ε/2) (1/4)
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  have hδε : 2*δ≤ε := by have hh := min_le_left (ε/2) (1/4); dsimp [δ]; linarith
  have hδ1 : 2*δ≤1/2 := by have hh := min_le_right (ε/2) (1/4); dsimp [δ]; linarith
  obtain ⟨K,hK⟩ := exists_nat_gt (2/δ)
  have hKr : 0<(K : ℝ) := (div_pos (by norm_num) hδ).trans hK
  have hKp : 0<K := by exact_mod_cast hKr
  have hKδ : 2<δ*((K : ℝ)+2) := by
    have hh := (div_lt_iff₀ hδ).mp hK
    nlinarith
  obtain ⟨U,hU,hd,hcover⟩ := exists_rohlin_tower μ e he (N:=((K+2)*n)) (Nat.mul_pos (by omega) hn) hδ
  have hmp := he.toMeasurePreserving
  let T : Set X := ⋃ i : Fin ((K+2)*n),(e^[i.val]) '' U
  let M : Set X := middleTower e U n K
  have hT : MeasurableSet T := MeasurableSet.iUnion (fun i => measurableSet_iterate_image e hU i.val)
  have hM : MeasurableSet M := measurableSet_middleTower e hU n K
  have hTm : μ.real T=(((K : ℝ)+2)*(n : ℝ))*μ.real U := by
    have hh := congrArg ENNReal.toReal (tower_measure μ e hmp hU ((K+2)*n) hd)
    rw [ENNReal.toReal_mul,ENNReal.toReal_natCast] at hh
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Measure.real,T] using hh
  have hMm : μ.real M=((K : ℝ)*(n : ℝ))*μ.real U := by
    have hh := congrArg ENNReal.toReal (middleTower_measure μ e hmp hU hn hd)
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,Nat.cast_mul,Measure.real,M] using hh
  have hTc : μ.real T+μ.real Tᶜ=1 := by
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using
      measureReal_add_measureReal_compl (μ:=μ) hT
  have hTcδ : μ.real Tᶜ<δ := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hcover
    simpa only [ENNReal.toReal_ofReal hδ.le,T,Measure.real] using hh
  have hTm1 : μ.real T≤1 := by
    have hh : 0≤μ.real Tᶜ := ENNReal.toReal_nonneg
    linarith
  have hcap : 2*((n : ℝ)*μ.real U)<δ := by
    have hK2 : 0<(K : ℝ)+2 := by positivity
    have hh : ((K : ℝ)+2)*(2*((n : ℝ)*μ.real U))<((K : ℝ)+2)*δ := by
      rw [hTm] at hTm1
      nlinarith
    nlinarith
  have herror : 1-μ.real M<2*δ := by rw [hTm] at hTc; rw [hMm]; nlinarith
  have hMpR : 0<μ.real M := by linarith
  have hMp : 0<μ M := (ENNReal.toReal_pos_iff.mp hMpR).1
  have hUpR : 0<μ.real U := by
    have hu0 : 0≤μ.real U := ENNReal.toReal_nonneg
    by_contra hbad
    have hz := le_antisymm (le_of_not_gt hbad) hu0
    rw [hMm,hz,mul_zero] at hMpR
    linarith
  have hUp : 0<μ U := (ENNReal.toReal_pos_iff.mp hUpR).1
  obtain ⟨V,hV,hdV,hmap,hVm⟩ := exists_unbiased_block_base μ e hmp hU hn hd p hp
  have hVp : 0<μ V := by
    rw [hVm]
    exact ENNReal.mul_pos (by exact_mod_cast hKp.ne') hUp.ne'
  have hVcover : μ (⋃ i : Fin n,(e^[i.val]) '' V)=μ M := by
    rw [tower_measure μ e hmp hV n hdV,hVm,middleTower_measure μ e hmp hU hn hd]
    push_cast
    ring
  have hVmeas : MeasurableSet (⋃ i : Fin n,(e^[i.val]) '' V) :=
    MeasurableSet.iUnion (fun i => measurableSet_iterate_image e hV i.val)
  have hVcomp : μ.real (⋃ i : Fin n,(e^[i.val]) '' V)ᶜ=1-μ.real M := by
    have hh := measureReal_add_measureReal_compl (μ:=μ) hVmeas
    simp only [Measure.real,hVcover,measure_univ,ENNReal.toReal_one] at hh
    change (μ _).toReal=1-(μ M).toReal
    linarith
  have hn0 : (n : ℝ≥0∞)≠0 := by exact_mod_cast hn.ne'
  have hnf : (n : ℝ≥0∞)≠⊤ := by simp
  have hnorm := normalize_scaled_observation (μ.restrict V) (μ.restrict M) p hp
    (ENNReal.inv_ne_zero.mpr hnf) (ENNReal.inv_ne_top.mpr hn0) hmap
  simp only [Measure.restrict_apply_univ] at hnorm
  refine ⟨V,hV,hVp,hdV,?_,?_⟩
  · rw [hVcomp]
    exact herror.trans_le hδε
  · rw [hnorm]
    intro D hD
    exact (normalized_restriction_observation_close μ hM hMp p hp D hD).trans (herror.le.trans hδε)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]

omit [StandardBorelSpace X] [Nonempty A] in
lemma paintTower_repaint_integral (μ : Measure X) [IsFiniteMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {U : Set X} (hU : MeasurableSet U) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    {B : X → (Fin N → A)} (hB : Measurable B) {p : X → A} (hp : Measurable p) :
    μ.real {x | p x≠paintTower e U N B p x}=
      ∫ x,nameCost (word e p N x) (B x) ∂μ.restrict U := by
  rw [Measure.real,paintTower_repaint μ e he hU N hd hB hp,
    ENNReal.toReal_sum (fun _ _ => measure_ne_top μ _)]
  simp only [nameCost,word]
  rw [integral_finsetSum _ (fun (i : Fin N) _ => integrable_finite_observation (μ.restrict U)
    (fun x => (p (e^[i.val] x),B x i))
    ((hp.comp (e.measurable.iterate i.val)).prodMk ((measurable_pi_apply i).comp hB))
    (fun ab => symbolCost ab.1 ab.2))]
  apply Finset.sum_congr rfl
  intro i _
  rw [finite_symbolCost_integral (μ.restrict U) (fun x => p (e^[i.val] x)) (fun x => B x i)
    (hp.comp (e.measurable.iterate i.val)) ((measurable_pi_apply i).comp hB)]
  have hm : MeasurableSet {x | p (e^[i.val] x)≠B x i} :=
    (measurableSet_eq_fun (hp.comp (e.measurable.iterate i.val)) ((measurable_pi_apply i).comp hB)).compl
  rw [Measure.real,Measure.restrict_apply hm,inter_comm]

theorem realize_tower_coupling (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {U : Set X} (hU : MeasurableSet U) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (p : X → A) (hp : Measurable p) (t : (Fin N → A) → ℝ)
    (R : MatrixCoupling (mass (μ.restrict U) (word e p N)) t) :
    ∃ q : X → A,Measurable q ∧
      (∀ a b,mass (μ.restrict U) (fun x => (word e p N x,word e q N x)) (a,b)=R.weight a b) ∧
      (∀ b,mass (μ.restrict U) (word e q N) b=t b) ∧
      μ.real {x | p x≠q x}=R.cost nameCost ∧
      ∀ x,x∉⋃ i : Fin N,(e^[i.val]) '' U → q x=p x := by
  obtain ⟨B,hB,hR⟩ := realize_finite_coupling_finite (μ.restrict U) (word e p N)
    (word_measurable e e.measurable p hp N) t R
  let q := paintTower e U N B p
  have hq : Measurable q := measurable_paintTower e hU N hd hB hp
  have hj (a b : Fin N → A) :
      mass (μ.restrict U) (fun x => (word e p N x,word e q N x)) (a,b)=R.weight a b := by
    rw [←hR a b]
    unfold mass
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [ae_restrict_mem hU] with x hx
    change ((word e p N x,word e q N x)=(a,b)) = ((word e p N x,B x)=(a,b))
    rw [show word e q N x=B x from paintTower_word e U N hd B p hx]
  refine ⟨q,hq,hj,?_,?_,fun x hx => paintTower_off e U N B p hx⟩
  · intro b
    rw [mass_joint_col (μ.restrict U) (word e p N) (word e q N)
      (word_measurable e e.measurable p hp N) (word_measurable e e.measurable q hq N)]
    simp_rw [hj]
    exact R.col b
  · exact (paintTower_repaint_integral μ e he hU N hd hB hp).trans
      (integral_cost_of_realization (μ.restrict U) (word e p N)
        (word_measurable e e.measurable p hp N) B hB R hR nameCost)

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Towers_ScaledFiniteCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X] [Fintype A] [Fintype B]

omit [Fintype A] in
lemma mass_smul_measure (μ : Measure X) (c : ℝ≥0∞) (p : X → A) (a : A) :
    mass (c • μ) p a=c.toReal*mass μ p a := by
  simp only [mass,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul]

omit [Fintype A] in
lemma normalize_mass_cancel (μ : Measure X) [IsFiniteMeasure μ] {U : Set X}
    (hU : 0<μ U) (p : X → A) (a : A) :
    μ.real U*mass ((μ U)⁻¹ • μ.restrict U) p a=mass (μ.restrict U) p a := by
  rw [Measure.real,mass_smul_measure,ENNReal.toReal_inv,←mul_assoc]
  rw [mul_inv_cancel₀ (ENNReal.toReal_pos hU.ne' (measure_ne_top _ _)).ne',one_mul]

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ}
lemma scale_cost (R : MatrixCoupling p q) (c : ℝ) (hc : 0 ≤ c) (d : A → B → ℝ) :
    (R.scale c hc).cost d=c*R.cost d := by
  simp only [cost,scale,mul_assoc,←Finset.mul_sum]
lemma cost_nonneg (R : MatrixCoupling p q) (d : A → B → ℝ) (hd : ∀ a b,0≤d a b) :
    0≤R.cost d :=
  Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => mul_nonneg (R.nonneg a b) (hd a b)))
end MatrixCoupling

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]

omit [StandardBorelSpace X] in
lemma normalized_restriction_probability (μ : Measure X) [IsFiniteMeasure μ]
    {U : Set X} (hU : 0<μ U) : IsProbabilityMeasure ((μ U)⁻¹ • μ.restrict U) := by
  constructor
  rw [Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hU.ne' (measure_ne_top _ _)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [StandardBorelSpace X] in
lemma base_mass_to_law (μ : Measure X) [IsFiniteMeasure μ] (ν : Measure Y) [IsFiniteMeasure ν]
    {U : Set X} {p : X → A} {q : Y → A} (hp : Measurable p) (hq : Measurable q)
    (h : ∀ a,mass (μ.restrict U) p a=μ.real U*mass ν q a) :
    (μ.restrict U).map p=μ U • ν.map q := by
  apply Measure.ext_of_singleton
  intro a
  have hright : (μ U • ν.map q) {a}≠⊤ := by
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hright).mp
  rw [Measure.map_apply hp (measurableSet_singleton a),Measure.smul_apply,smul_eq_mul,
    ENNReal.toReal_mul,Measure.map_apply hq (measurableSet_singleton a)]
  exact h a

omit [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace A]
  [Fintype A] [MeasurableSingletonClass A] in
lemma wordWindow_word (f : X → X) (p : X → A) {n m : ℕ} (i : ℕ) (hi : i+m≤n) (x : X) :
    wordWindow i hi (word f p n x)=word f p m (f^[i] x) := by
  funext j
  simp only [wordWindow,word,Function.iterate_add_apply]

omit [StandardBorelSpace X] in
lemma tower_interior_level_law (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (f : Y → Y) (hf : MeasurePreserving f ν ν) {U : Set X}
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    {n m : ℕ} (hbase : (μ.restrict U).map (word e p n)=μ U • ν.map (word f q n))
    (i : ℕ) (hi : i+m≤n) :
    (μ.restrict ((e^[i]) '' U)).map (word e p m)=μ U • ν.map (word f q m) := by
  have hpw := word_measurable e e.measurable p hp m
  have hqn := word_measurable f hf.measurable q hq n
  have hqm := word_measurable f hf.measurable q hq m
  have hW : Measurable (wordWindow (A:=A) i hi) := measurable_of_countable _
  have heI : MeasurePreserving (iterateEquiv e i) μ μ := by
    simpa only [funext (iterateEquiv_apply e i)] using he.iterate i
  change (μ.restrict ((iterateEquiv e i) '' U)).map (word e p m)=_
  rw [map_restrict_image_equiv μ (iterateEquiv e i) heI U (word e p m) hpw]
  have hcomp : word e p m ∘ iterateEquiv e i=wordWindow i hi ∘ word e p n := by
    funext x
    exact (wordWindow_word e p i hi x).symm
  rw [hcomp,←Measure.map_map hW (word_measurable e e.measurable p hp n),hbase,
    Measure.map_smul,Measure.map_map hW hqn]
  have hcomp' : wordWindow i hi ∘ word f q n=word f q m ∘ f^[i] := by
    funext y
    exact wordWindow_word f q i hi y
  rw [hcomp',←Measure.map_map hqm (hf.measurable.iterate i),(hf.iterate i).map_eq]

omit [StandardBorelSpace X] in
lemma tower_interior_law (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (f : Y → Y) (hf : MeasurePreserving f ν ν) {U : Set X} (hU : MeasurableSet U)
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    {n m : ℕ} (hm : m≤n)
    (hd : Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (hbase : (μ.restrict U).map (word e p n)=μ U • ν.map (word f q n)) :
    (μ.restrict (⋃ i : Fin (n-m),(e^[i.val]) '' U)).map (word e p m)=
      (((n-m : ℕ) : ℝ≥0∞)*μ U) • ν.map (word f q m) := by
  have hd' : Pairwise (fun i j : Fin (n-m) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)) := by
    intro i j hij
    apply hd (i:=⟨i.val,by omega⟩) (j:=⟨j.val,by omega⟩)
    intro hh
    exact hij (Fin.ext (congrArg (fun z : Fin n => z.val) hh))
  rw [map_restrict_finite_iUnion μ (fun i : Fin (n-m) => (e^[i.val]) '' U) (fun i => measurableSet_iterate_image e hU i.val) hd' _
    (word_measurable e e.measurable p hp m)]
  have hi (i : Fin (n-m)) := tower_interior_level_law μ ν e he f hf p q hp hq (m:=m) hbase i.val (by omega)
  simp_rw [hi]
  rw [←Finset.sum_smul]
  congr 1
  simp [nsmul_eq_mul]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [StandardBorelSpace X] in
theorem tower_short_word_lawClose (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (f : Y → Y) (hf : MeasurePreserving f ν ν) {U : Set X} (hU : MeasurableSet U) (hUp : 0<μ U)
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    {n m : ℕ} (hm : m<n)
    (hd : Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (hbase : (μ.restrict U).map (word e p n)=μ U • ν.map (word f q n))
    {ε : ℝ} (hcover : μ.real (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ<ε) :
    LawClose (μ.map (word e p m)) (ν.map (word f q m)) (ε+(m : ℝ)/(n : ℝ)) := by
  let C : Set X := ⋃ i : Fin (n-m),(e^[i.val]) '' U
  let T : Set X := ⋃ i : Fin n,(e^[i.val]) '' U
  have hC : MeasurableSet C := MeasurableSet.iUnion (fun i => measurableSet_iterate_image e hU i.val)
  have hT : MeasurableSet T := MeasurableSet.iUnion (fun i => measurableSet_iterate_image e hU i.val)
  have hd' : Pairwise (fun i j : Fin (n-m) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)) := by
    intro i j hij
    apply hd (i:=⟨i.val,by omega⟩) (j:=⟨j.val,by omega⟩)
    intro hh
    exact hij (Fin.ext (congrArg (fun z : Fin n => z.val) hh))
  have hCm : μ C=((n-m : ℕ) : ℝ≥0∞)*μ U := tower_measure μ e he hU (n-m) hd'
  have hTm : μ T=(n : ℝ≥0∞)*μ U := tower_measure μ e he hU n hd
  have hCp : 0<μ C := by
    rw [hCm]
    exact ENNReal.mul_pos (by exact_mod_cast (show 0<n-m by omega).ne') hUp.ne'
  have hCr : μ.real C=((n : ℝ)-(m : ℝ))*μ.real U := by
    change (μ C).toReal=_
    rw [hCm,ENNReal.toReal_mul,ENNReal.toReal_natCast,Nat.cast_sub hm.le]
    rfl
  have hTr : μ.real T=(n : ℝ)*μ.real U := by
    change (μ T).toReal=_
    rw [hTm,ENNReal.toReal_mul,ENNReal.toReal_natCast]
    rfl
  have hi := tower_interior_law μ ν e he f hf hU p q hp hq hm.le hd hbase
  have hnorm : (((μ C)⁻¹ • μ.restrict C).map (word e p m))=ν.map (word f q m) := by
    rw [Measure.map_smul]
    rw [hi,←hCm,smul_smul,ENNReal.inv_mul_cancel hCp.ne' (measure_ne_top _ _),one_smul]
  have hclose := (normalized_restriction_observation_close μ hC hCp (word e p m)
    (word_measurable e e.measurable p hp m)).symm
  rw [hnorm] at hclose
  have hTc : μ.real T+μ.real Tᶜ=1 := by
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using
      measureReal_add_measureReal_compl (μ:=μ) hT
  have hTr1 : (n : ℝ)*μ.real U≤1 := by
    have hnon : 0≤μ.real Tᶜ := ENNReal.toReal_nonneg
    rw [hTr] at hTc
    linarith
  have hn : 0<(n : ℝ) := by exact_mod_cast (show 0<n by omega)
  have hbound : (m : ℝ)*μ.real U≤(m : ℝ)/(n : ℝ) := by
    apply (le_div_iff₀ hn).mpr
    have hh := mul_le_mul_of_nonneg_left hTr1 (Nat.cast_nonneg m)
    nlinarith
  intro D hD
  apply (hclose D hD).trans
  rw [hCr]
  rw [hTr] at hTc
  have hc : μ.real Tᶜ<ε := hcover
  nlinarith

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_DecodedTowerCopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A C : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C] in
lemma nameCost_le_prefixNameCost {k t : ℕ} (F : C → A)
    (a : Fin (k+t) → C) (b : Fin (k+t) → A) :
    nameCost (F ∘ a) b ≤ prefixNameCost F (fun i => a (Fin.castAdd t i)) b + t := by
  rw [nameCost,Fin.sum_univ_add]
  unfold prefixNameCost
  apply add_le_add_right
  calc
    (∑ i : Fin t,symbolCost (F (a (Fin.natAdd k i))) (b (Fin.natAdd k i))) ≤
        ∑ _ : Fin t,(1 : ℝ) := Finset.sum_le_sum (fun _ _ => symbolCost_le_one _ _)
    _ = (t : ℝ) := by simp

theorem realize_prefix_tower_coupling (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {U : Set X} (hU : MeasurableSet U) (k t : ℕ)
    (hd : Pairwise (fun i j : Fin (k+t) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (p : X → C) (hp : Measurable p) (F : C → A) (v : (Fin (k+t) → A) → ℝ)
    (R : MatrixCoupling (mass (μ.restrict U) (word e p k)) v) :
    ∃ q : X → A,Measurable q ∧
      (∀ a b,mass (μ.restrict U) (fun x => (word e p k x,word e q (k+t) x)) (a,b)=R.weight a b) ∧
      (∀ b,mass (μ.restrict U) (word e q (k+t)) b=v b) ∧
      μ.real {x | F (p x)≠q x}≤R.cost (prefixNameCost F)+(t : ℝ)*μ.real U ∧
      ∀ x,x∉⋃ i : Fin (k+t),(e^[i.val]) '' U → q x=F (p x) := by
  have hF : Measurable F := measurable_of_countable F
  have hpw := word_measurable e e.measurable p hp k
  obtain ⟨B,hB,hR⟩ := realize_finite_coupling_finite (μ.restrict U) (word e p k) hpw v R
  let q := paintTower e U (k+t) B (F ∘ p)
  have hq : Measurable q := measurable_paintTower e hU (k+t) hd hB (hF.comp hp)
  have hj (a : Fin k → C) (b : Fin (k+t) → A) :
      mass (μ.restrict U) (fun x => (word e p k x,word e q (k+t) x)) (a,b)=R.weight a b := by
    rw [←hR a b]
    unfold mass
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [ae_restrict_mem hU] with x hx
    change ((word e p k x,word e q (k+t) x)=(a,b)) = ((word e p k x,B x)=(a,b))
    rw [show word e q (k+t) x=B x from paintTower_word e U (k+t) hd B (F ∘ p) hx]
  refine ⟨q,hq,hj,?_,?_,fun x hx => paintTower_off e U (k+t) B (F ∘ p) hx⟩
  · intro b
    rw [mass_joint_col (μ.restrict U) (word e p k) (word e q (k+t)) hpw
      (word_measurable e e.measurable q hq (k+t))]
    simp_rw [hj]
    exact R.col b
  · change μ.real {x | (F ∘ p) x≠q x}≤_
    rw [paintTower_repaint_integral μ e he hU (k+t) hd hB (hF.comp hp)]
    have hprefix : Integrable (fun x => prefixNameCost F (word e p k x) (B x)) (μ.restrict U) :=
      integrable_finite_observation (μ.restrict U) (fun x => (word e p k x,B x))
        (hpw.prodMk hB) (fun ab => prefixNameCost F ab.1 ab.2)
    have hfull : Integrable (fun x => nameCost (word e (F ∘ p) (k+t) x) (B x)) (μ.restrict U) :=
      integrable_finite_observation (μ.restrict U) (fun x => (word e (F ∘ p) (k+t) x,B x))
        ((word_measurable e e.measurable (F ∘ p) (hF.comp hp) (k+t)).prodMk hB)
        (fun ab => nameCost ab.1 ab.2)
    have hb := integral_mono hfull (hprefix.add (integrable_const (t : ℝ)))
      (fun x => nameCost_le_prefixNameCost F (word e p (k+t) x) (B x))
    dsimp only [Pi.add_apply] at hb
    rw [integral_add hprefix (integrable_const (t : ℝ)), integral_const] at hb
    rw [integral_cost_of_realization (μ.restrict U) (word e p k) hpw B hB R hR (prefixNameCost F)] at hb
    simpa only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hb

omit [StandardBorelSpace X] [Nonempty A] in
lemma prefix_tower_decoder_error (μ : Measure X) [IsFiniteMeasure μ]
    (e : X ≃ᵐ X) {U : Set X} (_hU : MeasurableSet U) (k t : ℕ)
    (p : X → C) (q : X → A) (hp : Measurable p) (hq : Measurable q)
    {v : (Fin (k+t) → A) → ℝ} (R : MatrixCoupling (mass (μ.restrict U) (word e p k)) v)
    (hR : ∀ a b,mass (μ.restrict U) (fun x => (word e p k x,word e q (k+t) x)) (a,b)=R.weight a b)
    (D : (Fin (k+t) → A) → (Fin k → C)) :
    μ.real (U∩{x | D (word e q (k+t) x)≠word e p k x})=
      R.cost (fun a b => symbolCost a (D b)) := by
  have hpw := word_measurable e e.measurable p hp k
  have hqw := word_measurable e e.measurable q hq (k+t)
  have hD : Measurable D := measurable_of_countable D
  have hh := finite_symbolCost_integral (μ.restrict U) (word e p k) (D ∘ word e q (k+t)) hpw (hD.comp hqw)
  have heq : (μ.restrict U).real {x | word e p k x≠(D ∘ word e q (k+t)) x}=
      μ.real (U∩{x | D (word e q (k+t) x)≠word e p k x}) := by
    have hm : MeasurableSet {x | word e p k x≠(D ∘ word e q (k+t)) x} :=
      (measurableSet_eq_fun hpw (hD.comp hqw)).compl
    rw [Measure.real,Measure.real,Measure.restrict_apply hm,inter_comm]
    congr 2
    ext x
    simp only [mem_inter_iff,mem_ofPred_eq,Function.comp_apply,ne_comm]
  rw [heq] at hh
  exact hh.symm.trans (integral_cost_of_realization (μ.restrict U) (word e p k) hpw
    (word e q (k+t)) hqw R hR (fun a b => symbolCost a (D b)))

omit [StandardBorelSpace X] [MeasurableSpace C] [MeasurableSingletonClass C] in
lemma ae_observation_of_zero_bad_mass (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → C) (Q : C → Prop) (hbad : ∀ c,¬Q c → mass μ p c=0) :
    ∀ᵐ x ∂μ,Q (p x) := by
  have hh (c : C) : ∀ᵐ x ∂μ,p x=c → Q c := by
    by_cases hc : Q c
    · exact ae_of_all _ (fun _ _ => hc)
    · apply ae_iff.mpr
      have hz : μ (p ⁻¹' {c})=0 := by
        have ht := hbad c hc
        change (μ (p ⁻¹' {c})).toReal=0 at ht
        exact ((ENNReal.toReal_eq_zero_iff _).mp ht).resolve_right (measure_ne_top _ _)
      convert hz using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq,mem_preimage,mem_singleton_iff,hc,imp_false,not_not]
  filter_upwards [ae_all_iff.mpr hh] with x hx
  exact hx (p x) rfl

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A C : Type*} {k t r : ℕ}

lemma prefixNameCost_nonneg (F : C → A) (a : Fin k → C) (b : Fin (k+t) → A) :
    0 ≤ prefixNameCost F a b :=
  Finset.sum_nonneg (fun _ _ => symbolCost_nonneg _ _)

lemma prefixNameCost_le_length (F : C → A) (a : Fin k → C) (b : Fin (k+t) → A) :
    prefixNameCost F a b ≤ (k : ℝ) := by
  calc
    _ ≤ ∑ _ : Fin k,(1 : ℝ) := Finset.sum_le_sum (fun _ _ => symbolCost_le_one _ _)
    _ = _ := by simp

lemma prefixNameCost_modify (F : C → A) (a : Fin k → C) (b d : Fin (k+t) → A) :
    prefixNameCost F a d ≤ prefixNameCost F a b+nameCost b d := by
  have htri : prefixNameCost F a d ≤ prefixNameCost F a b+
      ∑ i : Fin k,symbolCost (b (Fin.castAdd t i)) (d (Fin.castAdd t i)) := by
    unfold prefixNameCost
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun _ _ => symbolCost_triangle _ _ _)
  apply htri.trans
  apply add_le_add_right
  rw [nameCost,Fin.sum_univ_add]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => symbolCost_nonneg _ _))

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]

theorem unsanitize_tower (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {U : Set X} (hU : MeasurableSet U)
    (n : ℕ) (hd : Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (p : X → A) (hp : Measurable p) (v : (Fin n → A) → ℝ)
    (hv : ∀ w,0≤v w) (hs : ∑ w,v w=1)
    (g : (Fin n → A) → (Fin n → A)) (K : ℝ) (hK : ∀ w,nameCost (g w) w≤K)
    (hbase : ∀ w,mass (μ.restrict U) (word e p n) w=μ.real U*pushWeight v g w) :
    ∃ q : X → A,Measurable q ∧
      (∀ w,mass (μ.restrict U) (word e q n) w=μ.real U*v w) ∧
      μ.real {x | p x≠q x}≤K*μ.real U := by
  classical
  let R : MatrixCoupling (mass (μ.restrict U) (word e p n)) (fun w => μ.real U*v w) := {
    weight := fun a b => if g b=a then μ.real U*v b else 0
    nonneg := fun a b => by split_ifs; exact mul_nonneg measureReal_nonneg (hv b); exact le_rfl
    row := fun a => by
      rw [hbase]
      simp only [pushWeight,Finset.mul_sum,mul_ite,mul_zero]
    col := fun b => by simp }
  obtain ⟨q,hq,_hjoint,hqbase,hcost,_hoff⟩ := realize_tower_coupling μ e he hU n hd p hp _ R
  refine ⟨q,hq,hqbase,?_⟩
  rw [hcost]
  change (∑ a,∑ b,(if g b=a then μ.real U*v b else 0)*nameCost a b)≤_
  rw [Finset.sum_comm]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  calc
    _ ≤ ∑ b,μ.real U*v b*K := Finset.sum_le_sum (fun b _ =>
      mul_le_mul_of_nonneg_left (hK b) (mul_nonneg measureReal_nonneg (hv b)))
    _ = K*μ.real U := by rw [←Finset.sum_mul,←Finset.mul_sum,hs,mul_one,mul_comm]

omit [StandardBorelSpace X] [Nonempty A] in
lemma word_disagreement_le (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p q : X → A)
    (hp : Measurable p) (hq : Measurable q) (m : ℕ) :
    μ.real {x | word f p m x≠word f q m x}≤(m : ℝ)*μ.real {x | p x≠q x} := by
  have hset : {x | word f p m x≠word f q m x}=
      ⋃ i : Fin m,(f^[i.val]) ⁻¹' {x | p x≠q x} := by
    ext x
    simp only [mem_ofPred_eq,mem_iUnion,mem_preimage]
    constructor
    · intro hx
      by_contra hn
      apply hx
      funext i
      have hh : ∀ i : Fin m,p (f^[i.val] x)=q (f^[i.val] x) := by simpa using hn
      exact hh i
    · rintro ⟨i,hi⟩ h
      exact hi (congrFun h i)
  rw [hset]
  apply (measureReal_iUnion_fintype_le _).trans
  have hE : MeasurableSet {x | p x≠q x} := (measurableSet_eq_fun hp hq).compl
  have he (i : Fin m) : μ.real ((f^[i.val]) ⁻¹' {x | p x≠q x})=μ.real {x | p x≠q x} := by
    rw [Measure.real,Measure.real,(hf.iterate i.val).measure_preimage hE.nullMeasurableSet]
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,le_refl]

omit [StandardBorelSpace X] [Nonempty A] in
lemma word_lawClose_of_repaint (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p q : X → A)
    (hp : Measurable p) (hq : Measurable q) (m : ℕ) :
    LawClose (μ.map (word f p m)) (μ.map (word f q m)) ((m : ℝ)*μ.real {x | p x≠q x}) := by
  intro D hD
  exact (law_distance_le_disagreement μ (word_measurable f hf.measurable p hp m)
    (word_measurable f hf.measurable q hq m) hD).trans (word_disagreement_le μ f hf p q hp hq m)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A C : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C] [Nonempty C]

omit [StandardBorelSpace X] [TopologicalSpace X] [SecondCountableTopology X]
  [OpensMeasurableSpace X] in
lemma tower_real_mass_le_one (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {U : Set X} (hU : MeasurableSet U)
    (n : ℕ) (hd : Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U))) :
    (n : ℝ)*μ.real U≤1 := by
  have hh := congrArg ENNReal.toReal (tower_measure μ e he hU n hd)
  rw [ENNReal.toReal_mul,ENNReal.toReal_natCast] at hh
  have hi := measureReal_mono (μ:=μ) (subset_univ (⋃ i : Fin n,(e^[i.val]) '' U))
  simpa only [Measure.real,measure_univ,ENNReal.toReal_one,hh] using hi

omit [StandardBorelSpace X] [TopologicalSpace X] [SecondCountableTopology X]
  [OpensMeasurableSpace X] in
lemma tower_suffix_mass_le (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {U : Set X} (hU : MeasurableSet U)
    {k t : ℕ} (hn : 0<k+t)
    (hd : Pairwise (fun i j : Fin (k+t) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U))) :
    (t : ℝ)*μ.real U≤(t : ℝ)/(k+t : ℕ) := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr hn)).mpr
  have hh := mul_le_mul_of_nonneg_left (tower_real_mass_le_one μ e he hU (k+t) hd) (Nat.cast_nonneg t)
  nlinarith

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_SanitizedTowerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [MeasurableSpace A] [Fintype A] [DecidableEq A]
    [MeasurableSingletonClass A] [Nonempty A]

theorem sanitized_tower_short_word_lawClose
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (f : Y → Y) (hf : MeasurePreserving f ν ν)
    {U : Set X} (hU : MeasurableSet U) (hUp : 0<μ U)
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    {n m : ℕ} (hm : m<n)
    (hd : Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (g : (Fin n → A) → (Fin n → A)) {K : ℝ} (hK0 : 0≤K) (hK : ∀ w,nameCost (g w) w≤K)
    (hbase : ∀ w,mass (μ.restrict U) (word e p n) w=
      μ.real U*pushWeight (mass ν (word f q n)) g w)
    {ε : ℝ} (hcover : μ.real (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ<ε) :
    LawClose (μ.map (word e p m)) (ν.map (word f q m))
      (ε+(m : ℝ)/(n : ℝ)+(m : ℝ)*K/(n : ℝ)) := by
  have hqw := word_measurable f hf.measurable q hq n
  have hv : ∀ w,0 ≤ mass ν (word f q n) w := fun w => mass_nonneg _ _ _
  have hs : (∑ w,mass ν (word f q n) w)=1 := by rw [mass_sum ν _ hqw]; simp
  obtain ⟨r,hr,hrbase,hpaint⟩ := unsanitize_tower μ e he hU n hd p hp _ hv hs g K hK hbase
  have hbaseMap := base_mass_to_law μ ν (word_measurable e e.measurable r hr n) hqw hrbase
  have hraw := tower_short_word_lawClose μ ν e he f hf hU hUp r q hr hq hm hd hbaseMap hcover
  have hclose := (word_lawClose_of_repaint μ e he p r hp hr m).triangle hraw
  apply hclose.mono
  have hn : (0 : ℝ)<n := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le m) hm)
  have hmass : (n : ℝ)*μ.real U≤1 := by
    have hh := congrArg ENNReal.toReal (tower_measure μ e he hU n hd)
    rw [ENNReal.toReal_mul,ENNReal.toReal_natCast] at hh
    have hi := measureReal_mono (μ:=μ) (subset_univ (⋃ i : Fin n,(e^[i.val]) '' U))
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one,hh] using hi
  have hb : K*μ.real U≤K/(n : ℝ) := by
    apply (le_div_iff₀ hn).mpr
    have hh := mul_le_mul_of_nonneg_left hmass hK0
    nlinarith
  have hh := mul_le_mul_of_nonneg_left (hpaint.trans hb) (Nat.cast_nonneg m)
  rw [←mul_div_assoc] at hh
  linarith

lemma marked_tower_short_word_lawClose
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (f : Y → Y) (hf : MeasurePreserving f ν ν)
    {U : Set X} (hU : MeasurableSet U) (hUp : 0<μ U)
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    {n m r : ℕ} (hm : m<n)
    (hd : Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (zero one : A)
    (hbase : ∀ w,mass (μ.restrict U) (word e p n) w=
      μ.real U*pushWeight (mass ν (word f q n)) (Marker.markWord r zero one) w)
    {ε : ℝ} (hcover : μ.real (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ<ε) :
    LawClose (μ.map (word e p m)) (ν.map (word f q m))
      (ε+(m : ℝ)/(n : ℝ)+(m : ℝ)*(Marker.reserved n r).card/(n : ℝ)) := by
  apply sanitized_tower_short_word_lawClose μ ν e he f hf hU hUp p q hp hq hm hd
    (Marker.markWord r zero one) (Nat.cast_nonneg _) _ hbase hcover
  intro w
  rw [nameCost_comm]
  exact Marker.markWord_cost zero one w

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy Filter
open scoped BigOperators ENNReal Topology
variable {X A C : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace C] [Fintype C] [DecidableEq C] [MeasurableSingletonClass C] [Nonempty C]

omit [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] in
lemma marked_pushWeight_support {n r : ℕ} (v : (Fin n → A) → ℝ) (hr0 : 0 < r) (hr : r < n)
    (zero one : A) (w : Fin n → A) (hw : ¬Marker.MarkedBlock hr zero one w) :
    pushWeight v (Marker.markWord r zero one) w=0 := by
  unfold pushWeight
  apply Finset.sum_eq_zero
  intro b _
  have hne : Marker.markWord r zero one b≠w := by
    intro h
    exact hw (h ▸ Marker.markWord_isMarked hr0 hr zero one b)
  simp only [ite_eq_right hne]

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_RelativeFiniteRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [StandardBorelSpace X] in
lemma tower_disjoint_mono (e : X ≃ᵐ X) (V : Set X) {N M : ℕ} (hm : M≤N)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' V) ((e^[j.val]) '' V))) :
    Pairwise (fun i j : Fin M => Disjoint ((e^[i.val]) '' V) ((e^[j.val]) '' V)) := by
  intro i j hij
  apply hd (i:=⟨i.val,i.isLt.trans_le hm⟩) (j:=⟨j.val,j.isLt.trans_le hm⟩)
  intro hh
  exact hij (Fin.ext (congrArg (fun z : Fin N => z.val) hh))

omit [StandardBorelSpace X] in
lemma tower_interior_compl_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {U : Set X} (hU : MeasurableSet U)
    {N m : ℕ} (hN : 0<N) (hm : m≤N)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U))) :
    μ.real (⋃ i : Fin (N-m),(e^[i.val]) '' U)ᶜ≤
      μ.real (⋃ i : Fin N,(e^[i.val]) '' U)ᶜ+(m : ℝ)/(N : ℝ) := by
  have hc := congrArg ENNReal.toReal (tower_measure μ e he hU (N-m)
    (tower_disjoint_mono e U (Nat.sub_le N m) hd))
  have ht := congrArg ENNReal.toReal (tower_measure μ e he hU N hd)
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,Nat.cast_sub hm] at hc ht
  change μ.real (⋃ i : Fin (N-m),(e^[i.val]) '' U)=((N : ℝ)-m)*μ.real U at hc
  change μ.real (⋃ i : Fin N,(e^[i.val]) '' U)=(N : ℝ)*μ.real U at ht
  have hC := measureReal_add_measureReal_compl (μ:=μ)
    (MeasurableSet.iUnion (fun i : Fin (N-m) => measurableSet_iterate_image e hU i.val))
  have hT := measureReal_add_measureReal_compl (μ:=μ)
    (MeasurableSet.iUnion (fun i : Fin N => measurableSet_iterate_image e hU i.val))
  have hu : μ.real univ=1 := by simp [Measure.real]
  rw [hu,hc] at hC
  rw [hu,ht] at hT
  have hmass : (N : ℝ)*μ.real U≤1 := by
    linarith [measureReal_nonneg (μ:=μ) (s:=(⋃ i : Fin N,(e^[i.val]) '' U)ᶜ)]
  have hbound : (m : ℝ)*μ.real U≤(m : ℝ)/(N : ℝ) := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr hN)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg m)]
  linarith
end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_FixedWindowCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators
variable {A B C : Type*} {k t R : ℕ}

lemma decoderNameCost_nonneg (H : C → B) (D : (Fin (2*R+1) → A) → B)
    (a : Fin k → C) (b : Fin (k+t) → A) : 0≤decoderNameCost H D a b :=
  Finset.sum_nonneg (fun _ _ => symbolCost_nonneg _ _)
lemma decoderNameCost_le_length (H : C → B) (D : (Fin (2*R+1) → A) → B)
    (a : Fin k → C) (b : Fin (k+t) → A) : decoderNameCost H D a b≤(k-2*R : ℕ) := by
  calc
    _≤∑ _ : Fin (k-2*R),(1 : ℝ) := Finset.sum_le_sum (fun _ _ => symbolCost_le_one _ _)
    _=_ := by simp
lemma fixedWindowCost_nonneg (F : C → A) (H : C → B) (D : (Fin (2*R+1) → A) → B)
    (a : Fin k → C) (b : Fin (k+t) → A) : 0≤fixedWindowCost F H D a b :=
  div_nonneg (add_nonneg (prefixNameCost_nonneg F a b) (decoderNameCost_nonneg H D a b)) (by positivity)
lemma fixedWindowCost_le_one (hn : 0<k+t) (F : C → A) (H : C → B)
    (D : (Fin (2*R+1) → A) → B) (a : Fin k → C) (b : Fin (k+t) → A) :
    fixedWindowCost F H D a b≤1 := by
  apply (div_le_one (by positivity : (0 : ℝ)<2*(k+t : ℕ))).mpr
  have h₁ := prefixNameCost_le_length F a b
  have h₂ := decoderNameCost_le_length H D a b
  have h₃ : ((k-2*R : ℕ) : ℝ)≤(k : ℝ) := by exact_mod_cast Nat.sub_le k (2*R)
  push_cast
  linarith

lemma symbolCost_factor_le (F : C → B) (a b : C) : symbolCost (F a) (F b)≤ symbolCost a b := by
  classical
  by_cases h : a=b
  · subst b; simp [symbolCost]
  · simpa only [symbolCost,ite_eq_right h] using symbolCost_le_one (F a) (F b)

lemma symbolCost_function_le_sum {ι : Type*} [Fintype ι] (a b : ι → A) :
    symbolCost a b≤∑ i,symbolCost (a i) (b i) := by
  classical
  by_cases h : a=b
  · subst b; simp [symbolCost]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    have hh := Finset.single_le_sum (fun i _ => symbolCost_nonneg (a i) (b i)) (Finset.mem_univ i)
    simpa only [symbolCost,ite_eq_right h,ite_eq_right hi] using hh

lemma sum_blockWindow_cost_le (b d : Fin (k+t) → A) :
    (∑ i : Fin (k-2*R),nameCost (blockWindow b i) (blockWindow d i))≤(2*R+1 : ℕ)*nameCost b d := by
  classical
  unfold nameCost
  rw [Finset.sum_comm]
  calc
    _≤∑ _ : Fin (2*R+1),∑ j : Fin (k+t),symbolCost (b j) (d j) := by
      apply Finset.sum_le_sum
      intro j _
      let f : Fin (k-2*R) → Fin (k+t) := fun i => ⟨i.val+j.val,by have:=i.isLt; have:=j.isLt; omega⟩
      have hf : Function.Injective f := by intro i i' h; have := congrArg Fin.val h; apply Fin.ext; dsimp [f] at this; omega
      calc
        _=(∑ z ∈ Finset.univ.image f,symbolCost (b z) (d z)) := (Finset.sum_image (fun i hi i' hi' h => hf h)).symm
        _≤_ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => symbolCost_nonneg (b i) (d i))
    _=_ := by simp

lemma decoderNameCost_modify (H : C → B) (D : (Fin (2*R+1) → A) → B)
    (a : Fin k → C) (b d : Fin (k+t) → A) :
    decoderNameCost H D a d≤decoderNameCost H D a b+(2*R+1 : ℕ)*nameCost b d := by
  have hi (i : Fin (k-2*R)) := symbolCost_triangle (H (blockCenter a i)) (D (blockWindow b i)) (D (blockWindow d i))
  have hj (i : Fin (k-2*R)) := (symbolCost_factor_le D (blockWindow b i) (blockWindow d i)).trans
    (symbolCost_function_le_sum (blockWindow b i) (blockWindow d i))
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hi i |>.trans (add_le_add_right (hj i) _))
  rw [Finset.sum_add_distrib] at hh
  exact hh.trans (add_le_add_right (sum_blockWindow_cost_le b d) _)

lemma fixedWindowCost_markWord [Fintype A] (F : C → A) (H : C → B)
    (D : (Fin (2*R+1) → A) → B) (a : Fin k → C) (b : Fin (k+t) → A)
    (r : ℕ) (zero one : A) :
    fixedWindowCost F H D a (Marker.markWord r zero one b)≤fixedWindowCost F H D a b+
      ((2*R+2 : ℕ) : ℝ)*(Marker.reserved (k+t) r).card/(2*(k+t : ℕ)) := by
  classical
  have hp := prefixNameCost_modify F a b (Marker.markWord r zero one b)
  have hd := decoderNameCost_modify H D a b (Marker.markWord r zero one b)
  have hm := Marker.markWord_cost (r:=r) zero one b
  unfold fixedWindowCost
  rw [←add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  push_cast at *
  nlinarith
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A C : Type*} [MeasurableSpace X]
  [Fintype A] [DecidableEq A] [Nonempty A]
  [MeasurableSpace C] [Fintype C] [DecidableEq C] [MeasurableSingletonClass C]

theorem synchronized_cost_producer [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ)
    (htotal : ∀ m : ℕ, 0 < m → Ergodic (f^[m]) μ)
    (p : X → C) (hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0<weightEntropy β) (hrate : rate μ f p≤weightEntropy β)
    (zero one : A) {ε : ℝ} (hε : 0<ε) :
    ∃ K r m : ℕ,0<K ∧ 0 < r ∧ 0 < m ∧ ∀ᶠ n : ℕ in atTop,
      0<n ∧ r<n*K*m+n*m ∧
      ((n*m : ℕ) : ℝ)/(n*K*m+n*m : ℕ)<ε ∧
      ((Marker.reserved (n*K*m+n*m) r).card : ℝ)/(n*K*m+n*m : ℕ)<ε ∧
      ∀ R : MatrixCoupling (mass μ (word f p (n*K*m))) (productWordWeight β (n*K*m+n*m)),
        ∀ (c : (Fin (n*K*m) → C) → (Fin (n*K*m+n*m) → A) → ℝ),
        (∀ a b,0 ≤ c a b) → (∀ a b,c a b≤1) →
        ∀ (d : ℝ), (∀ a b,c a (Marker.markWord r zero one b) ≤ c a b+d) →
        ∃ (D : (Fin (n*K*m+n*m) → A) → (Fin (n*K*m) → C))
          (H : MatrixCoupling (mass μ (word f p (n*K*m)))
            (pushWeight (productWordWeight β (n*K*m+n*m)) (Marker.markWord r zero one))),
          H.cost (fun a b => symbolCost a (D b))<ε ∧
          H.cost c<R.cost c+ε+d := by
  let θ : ℝ := min (ε/16) (1/16)
  have hθ : 0<θ := lt_min (by positivity) (by norm_num)
  have hθsmall : θ<1/4 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hθeps : θ≤ε/16 := min_le_left _ _
  obtain ⟨K,r,hK,hr,δ,hδ,_hsuffix,hparams⟩ := exists_entropy_slack_parameters
    (Fintype.card A) (weightEntropy β) ε (by exact_mod_cast Fintype.card_pos) hβentropy hε
  obtain ⟨m,hm,hsource⟩ := entropy_rate_codebook μ f hf htotal p hp hδ
  have hKgo : Tendsto (fun n : ℕ => n*K) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hK) tendsto_id
  have hNgo : Tendsto (fun n : ℕ => n*K*m+n*m) atTop atTop :=
    tendsto_atTop_mono (fun n => (Nat.le_mul_of_pos_right n hm).trans (Nat.le_add_left _ _)) tendsto_id
  have hM : 0<(1-4*θ)*MatrixCoupling.decodingThreshold (ε/2) :=
    mul_pos (by linarith) (MatrixCoupling.decodingThreshold_pos (by positivity))
  have hsource' := hKgo.eventually (hsource θ hθ)
  have htarget := hNgo.eventually (eventually_iid_typical_words β hβ hβsum hδ hθ)
  have hpar := hparams m hm ((1-4*θ)*MatrixCoupling.decodingThreshold (ε/2)) hM
  refine ⟨K,r,m,hK,hr,hm,?_⟩
  filter_upwards [hsource',htarget,hpar] with n hnS hnT hnP
  obtain ⟨S,hScard,hSbad⟩ := hnS
  obtain ⟨T,hT,hTbad⟩ := hnT
  obtain ⟨hn,hrn,htail,hreserve,hsize⟩ := hnP
  have hnn : 0<n*K*m+n*m := lt_trans hr hrn
  refine ⟨hn,hrn,htail,hreserve,?_⟩
  intro R c hc0 hc1 d hd
  have hsum : (∑ a,mass μ (word f p (n*K*m)) a)=1 := by
    rw [mass_sum μ _ (word_measurable f hf.measurable p hp _)]; simp
  have hScard' : (S.card : ℝ)≤Real.exp ((n*K*m : ℕ)*(weightEntropy β+δ)) :=
    hScard.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (add_le_add_left hrate δ) (Nat.cast_nonneg _)))
  have hSmall : (S.card : ℝ)*(2*(Fintype.card A : ℝ)^(Marker.reserved (n*K*m+n*m) r).card*
      Real.exp (-((n*K*m+n*m : ℕ) : ℝ)*(weightEntropy β-δ))) ≤
      (1-4*θ)*MatrixCoupling.decodingThreshold (ε/2) := by
    apply le_trans (mul_le_mul_of_nonneg_right hScard' (by positivity))
    convert hsize.le using 1 <;> first | rfl | ring
  obtain ⟨D,H,hD,hH⟩ := MatrixCoupling.marked_word_decodable_coupling β hβ hβsum
    (by positivity : 0<ε/2) hθ.le hθsmall R hsum S T
    (mass_codebook_lower μ _ (word_measurable f hf.measurable p hp _) S hSbad).le
    (L:=((n*K*m+n*m : ℕ) : ℝ)*(weightEntropy β-δ))
    (by simpa only [neg_mul] using hT) hTbad.le zero one (by simpa only [neg_mul] using hSmall)
    c hc0 hc1 d hd
  exact ⟨D,H,by linarith,by linarith⟩

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A : Type*} [MeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

lemma tower_error_integral [StandardBorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (e : X ≃ᵐ X)
    (he : MeasurePreserving e μ μ) {U : Set X} (hU : MeasurableSet U) (m : ℕ)
    (p q : X → A) (hp : Measurable p) (hq : Measurable q) :
    μ.real {x | p x≠q x}≤μ.real (⋃ i : Fin m,(e^[i.val]) '' U)ᶜ+
      ∫ b in U,∑ i : Fin m,symbolCost (p (e^[i.val] b)) (q (e^[i.val] b)) ∂μ := by
  let Bad := fun i : Fin m => U∩{b | p (e^[i.val] b)≠q (e^[i.val] b)}
  have hsub : {x | p x≠q x}⊆(⋃ i : Fin m,(e^[i.val]) '' U)ᶜ ∪
      ⋃ i : Fin m,(e^[i.val]) '' Bad i := by
    intro x hx
    by_cases ht : x∈⋃ i : Fin m,(e^[i.val]) '' U
    · obtain ⟨i,b,hb,rfl⟩ := mem_iUnion.mp ht
      exact Or.inr (mem_iUnion.mpr ⟨i,b,⟨hb,hx⟩,rfl⟩)
    · exact Or.inl ht
  have hbound : μ {x | p x≠q x}≤μ (⋃ i : Fin m,(e^[i.val]) '' U)ᶜ+∑ i : Fin m,μ (Bad i) := by
    calc
      _≤_ := measure_mono hsub
      _≤μ (⋃ i : Fin m,(e^[i.val]) '' U)ᶜ+μ (⋃ i : Fin m,(e^[i.val]) '' Bad i) := measure_union_le _ _
      _≤μ (⋃ i : Fin m,(e^[i.val]) '' U)ᶜ+∑' i : Fin m,μ ((e^[i.val]) '' Bad i) := add_le_add_right (measure_iUnion_le _) _
      _=_ := by simp only [measure_iterate_image μ e he,tsum_fintype]
  have hsumfin : (∑ i : Fin m,μ (Bad i))≠⊤ := ENNReal.sum_ne_top.mpr (fun i _ => measure_ne_top _ _)
  have hreal := ENNReal.toReal_mono (show μ (⋃ i : Fin m,(e^[i.val]) '' U)ᶜ+∑ i : Fin m,μ (Bad i)≠⊤ from ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,hsumfin⟩) hbound
  rw [ENNReal.toReal_add (measure_ne_top _ _) hsumfin,ENNReal.toReal_sum (by intro i hi; exact measure_ne_top _ _)] at hreal
  have hint (i : Fin m) : Integrable (fun b => symbolCost (p (e^[i.val] b)) (q (e^[i.val] b))) (μ.restrict U) :=
    integrable_finite_observation (μ.restrict U) (fun b => (p (e^[i.val] b),q (e^[i.val] b)))
      ((hp.comp (e.measurable.iterate i.val)).prodMk (hq.comp (e.measurable.iterate i.val)))
      (fun a => symbolCost a.1 a.2)
  rw [integral_finsetSum _ (fun i _ => hint i)]
  have heq (i : Fin m) : (∫ b in U,symbolCost (p (e^[i.val] b)) (q (e^[i.val] b)) ∂μ)=μ.real (Bad i) := by
    rw [finite_symbolCost_integral (μ.restrict U) (fun b => p (e^[i.val] b)) (fun b => q (e^[i.val] b)) (hp.comp (e.measurable.iterate i.val)) (hq.comp (e.measurable.iterate i.val))]
    rw [Measure.real,Measure.restrict_apply' hU,inter_comm]
    rfl
  simp only [heq]
  exact hreal
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A C : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]

lemma boundedCost_left_triangle {B D : Type*} (c : B → D → ℝ)
    (h0 : ∀ a b,0 ≤ c a b) (h1 : ∀ a b,c a b≤1) (a b : B) (d : D) :
    c a d≤ symbolCost a b+c b d := by
  classical
  by_cases h : a=b
  · subst b; simp [symbolCost]
  · simp only [symbolCost,ite_eq_right h]
    linarith [h0 b d,h1 a d]

theorem lift_cost_transport [Nonempty C] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    {k t r : ℕ} (hn : 0<k+t) (hr : r<k+t)
    (p : X → C) (hp : Measurable p) (F : C → A)
    (v : (Fin (k+t) → A) → ℝ) (R : MatrixCoupling (mass μ (word e p k)) v)
    (c : (Fin k → C) → (Fin (k+t) → A) → ℝ)
    (hc0 : ∀ a b,0 ≤ c a b) (hc1 : ∀ a b,c a b≤1)
    (zero one : A) (h01 : zero≠one)
    (hmark : ∀ w,¬Marker.MarkedBlock hr zero one w → v w=0)
    (D : (Fin (k+t) → A) → (Fin k → C)) (c₀ : C) {ε : ℝ} (hε : 0<ε) :
    ∃ (U : Set X) (q : X → A),MeasurableSet U ∧ 0<μ U ∧ Measurable q ∧
      Pairwise (fun i j : Fin (k+t) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)) ∧
      μ.real (⋃ i : Fin (k+t),(e^[i.val]) '' U)ᶜ<ε ∧
      (∀ b,mass (μ.restrict U) (word e q (k+t)) b=μ.real U*v b) ∧
      (∫ x in U,c (word e p k x) (word e q (k+t) x) ∂μ)≤μ.real U*(R.cost c+ε) ∧
      (∀ x,x∉⋃ i : Fin (k+t),(e^[i.val]) '' U → q x=F (p x)) ∧
      μ.real {x | Marker.decodeWindow hn hr zero one (extendPrefixDecoder D c₀)
        (word e q (2*(k+t)) (integerIterate e (-((k+t : ℕ) : ℤ)) x))≠p x} <
        2*ε+R.cost (fun a b => symbolCost a (D b))+(t : ℝ)/(k+t : ℕ) := by
  have hw := word_measurable e e.measurable p hp k
  obtain ⟨U,hU,hUp,hd,hcover,hclose⟩ := exists_unbiased_rohlin_tower μ e he hn (word e p k) hw hε
  let ν := (μ U)⁻¹ • μ.restrict U
  have : IsProbabilityMeasure ν := normalized_restriction_probability μ hUp
  obtain ⟨S,hS⟩ := coupling_of_observation_lawClose ν μ (word e p k) (word e p k) hw hw hclose
  have hC := S.comp_cost_le R symbolCost c c (boundedCost_left_triangle c hc0 hc1)
  have hD := S.comp_cost_le R symbolCost (fun a b => symbolCost a (D b))
    (fun a b => symbolCost a (D b)) (fun a b d => symbolCost_triangle a b (D d))
  have hc : 0≤μ.real U := measureReal_nonneg
  let W := (S.comp R).scale (μ.real U) hc
  let W' : MatrixCoupling (mass (μ.restrict U) (word e p k)) (fun b => μ.real U*v b) := {
    weight := W.weight
    nonneg := W.nonneg
    row := fun a => (W.row a).trans (normalize_mass_cancel μ hUp (word e p k) a)
    col := W.col }
  have hWC : W'.cost c≤μ.real U*(R.cost c+ε) := by
    change W.cost c≤_
    rw [MatrixCoupling.scale_cost]
    apply mul_le_mul_of_nonneg_left _ hc
    linarith
  have hWD : W'.cost (fun a b => symbolCost a (D b))≤
      μ.real U*(ε+R.cost (fun a b => symbolCost a (D b))) := by
    change W.cost _≤_
    rw [MatrixCoupling.scale_cost]
    exact mul_le_mul_of_nonneg_left (hD.trans (add_le_add hS le_rfl)) hc
  obtain ⟨q,hq,hjoint,hbase,_hpaint,hoff⟩ :=
    realize_prefix_tower_coupling μ e he.toMeasurePreserving hU k t hd p hp F _ W'
  have hmarked : ∀ᵐ b ∂μ.restrict U,Marker.MarkedBlock hr zero one (word e q (k+t) b) :=
    ae_observation_of_zero_bad_mass (μ.restrict U) (word e q (k+t))
      (Marker.MarkedBlock hr zero one) (fun w hw => by rw [hbase w,hmark w hw,mul_zero])
  have hb := marked_tower_prefix_decoder_error μ e he.toMeasurePreserving p q hn hr zero one h01 D c₀ hU hmarked
  rw [prefix_tower_decoder_error μ e hU k t p q hp hq W' hjoint D] at hb
  refine ⟨U,q,hU,hUp,hq,hd,hcover,hbase,?_,hoff,?_⟩
  · rw [integral_cost_of_realization (μ.restrict U) (word e p k) hw (word e q (k+t))
      (word_measurable e e.measurable q hq _) W' hjoint c]
    exact hWC
  · have hmass := tower_real_mass_le_one μ e he.toMeasurePreserving hU (k+t) hd
    have htail := tower_suffix_mass_le μ e he.toMeasurePreserving hU hn hd
    have hD0 := R.cost_nonneg (fun a b => symbolCost a (D b)) (fun _ _ => symbolCost_nonneg _ _)
    have hh := mul_le_mul_of_nonneg_right hmass
      (show 0≤ε+R.cost (fun a b => symbolCost a (D b)) by linarith)
    have hbound := mul_le_mul_of_nonneg_left hWD (Nat.cast_nonneg (k+t))
    nlinarith
end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_FixedWindowTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A B C : Type*}

lemma blockWindow_word [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (e : X → X) (q : X → A) {k t R : ℕ} (x : X) (i : Fin (k-2*R)) :
    blockWindow (word e q (k+t) x) i=word e q (2*R+1) (e^[i.val] x) := by
  funext j
  simp only [blockWindow,word]
  rw [Nat.add_comm i.val j.val,Function.iterate_add_apply]

lemma integrable_wordCost [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
    (μ : Measure X) [IsFiniteMeasure μ] (e : X → X) (he : Measurable e)
    (p : X → C) (q : X → A) (hp : Measurable p) (hq : Measurable q) (k n : ℕ)
    (c : (Fin k → C) → (Fin n → A) → ℝ) :
    Integrable (fun x => c (word e p k x) (word e q n x)) μ :=
  integrable_finite_observation μ (fun x => (word e p k x,word e q n x))
    ((word_measurable e he p hp k).prodMk (word_measurable e he q hq n)) (fun a => c a.1 a.2)

lemma fixedWindowCost_scale [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
    {k t R : ℕ} (hn : 0<k+t) (F : C → A) (H : C → B)
    (D : (Fin (2*R+1) → A) → B) (a : Fin k → C) (b : Fin (k+t) → A) :
    2*(k+t : ℕ)*fixedWindowCost F H D a b=prefixNameCost F a b+decoderNameCost H D a b := by
  unfold fixedWindowCost
  exact mul_div_cancel₀ _ (by positivity : (2*((k+t : ℕ) : ℝ))≠0)

variable [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]

theorem fixed_window_tower_bounds (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {U : Set X} (hU : MeasurableSet U)
    {k t R : ℕ} (hn : 0<k+t) (hR : 2*R≤k)
    (hd : Pairwise (fun i j : Fin (k+t) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (p : X → C) (q : X → A) (hp : Measurable p) (hq : Measurable q)
    (F : C → A) (H : C → B) (D : (Fin (2*R+1) → A) → B) :
    let I := ∫ x in U,fixedWindowCost F H D (word e p k x) (word e q (k+t) x) ∂μ
    (μ.real {x | F (p x)≠q x}≤μ.real (⋃ i : Fin (k+t),(e^[i.val]) '' U)ᶜ+
      (t : ℝ)/(k+t : ℕ)+2*(k+t : ℕ)*I) ∧
    (μ.real {x | H (p (e^[R] x))≠D (word e q (2*R+1) x)}≤
      μ.real (⋃ i : Fin (k+t),(e^[i.val]) '' U)ᶜ+
      ((t+2*R : ℕ) : ℝ)/(k+t : ℕ)+2*(k+t : ℕ)*I) := by
  intro I
  have hc := integrable_wordCost (μ.restrict U) e e.measurable p q hp hq k (k+t) (fixedWindowCost F H D)
  have hpref := integrable_wordCost (μ.restrict U) e e.measurable p q hp hq k (k+t) (prefixNameCost F)
  have hdec := integrable_wordCost (μ.restrict U) e e.measurable p q hp hq k (k+t) (decoderNameCost H D)
  have hscale : (∫ x in U,prefixNameCost F (word e p k x) (word e q (k+t) x) ∂μ)+
      (∫ x in U,decoderNameCost H D (word e p k x) (word e q (k+t) x) ∂μ)=2*(k+t : ℕ)*I := by
    rw [←integral_add hpref hdec]
    change (∫ x in U,prefixNameCost F (word e p k x) (word e q (k+t) x)+decoderNameCost H D (word e p k x) (word e q (k+t) x) ∂μ)=_
    simp_rw [←fixedWindowCost_scale hn F H D]
    exact integral_const_mul _ _
  have hpre0 := integral_nonneg (f:=fun x => prefixNameCost F (word e p k x) (word e q (k+t) x)) (fun x => prefixNameCost_nonneg F (word e p k x) (word e q (k+t) x)) (μ:=μ.restrict U)
  have hdec0 := integral_nonneg (f:=fun x => decoderNameCost H D (word e p k x) (word e q (k+t) x)) (fun x => decoderNameCost_nonneg H D (word e p k x) (word e q (k+t) x)) (μ:=μ.restrict U)
  constructor
  · have hb := tower_error_integral μ e he hU k (F ∘ p) q ((measurable_of_countable F).comp hp) hq
    have hc := tower_interior_compl_bound μ e he hU hn (show t≤k+t by omega) hd
    have hsub : k+t-t=k := by omega
    rw [hsub] at hc
    change μ.real {x | F (p x)≠q x}≤μ.real (⋃ i : Fin k,(e^[i.val]) '' U)ᶜ+
      ∫ x in U,prefixNameCost F (word e p k x) (word e q (k+t) x) ∂μ at hb
    linarith
  · have hH : Measurable (fun x => H (p (e^[R] x))) := (measurable_of_countable H).comp (hp.comp (e.measurable.iterate _))
    have hD : Measurable (fun x => D (word e q (2*R+1) x)) := (measurable_of_countable D).comp (word_measurable e e.measurable q hq _)
    have hb := tower_error_integral μ e he hU (k-2*R) _ _ hH hD
    have hc := tower_interior_compl_bound μ e he hU hn (show t+2*R≤k+t by omega) hd
    have hsub : k+t-(t+2*R)=k-2*R := by omega
    rw [hsub] at hc
    have heq (x : X) : (∑ i : Fin (k-2*R),symbolCost (H (p (e^[R] (e^[i.val] x))))
        (D (word e q (2*R+1) (e^[i.val] x))))=decoderNameCost H D (word e p k x) (word e q (k+t) x) := by
      unfold decoderNameCost
      apply Finset.sum_congr rfl
      intro i _
      rw [blockWindow_word]
      dsimp only [blockCenter,word]
      rw [Nat.add_comm i.val R,Function.iterate_add_apply]
    simp only [heq] at hb
    linarith
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A B C : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
  [MeasurableSpace C] [Fintype C] [DecidableEq C] [MeasurableSingletonClass C] [Nonempty C]

theorem actual_fixed_window_copy (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (p : X → C) (hp : Measurable p) (F : C → A) (H : C → B)
    (R : ℕ) (D : (Fin (2*R+1) → A) → B)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) (hrate : rate μ e p≤weightEntropy β)
    (zero one : A) (h01 : zero≠one) (l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K r m : ℕ,0 < K ∧ 0 < r ∧ 0 < m ∧ ∀ᶠ n : ℕ in atTop,
      0 < n ∧ ∀ W : MatrixCoupling (mass μ (word e p (n*K*m))) (productWordWeight β (n*K*m+n*m)),
        ∃ (q : X → A) (s : ℤ) (M : ℕ) (G : (Fin M → A) → C),Measurable q ∧
          μ.real {x | F (p x)≠q x} < 2*W.cost (fixedWindowCost F H D)+ε ∧
          μ.real {x | H (p (e^[R] x))≠D (word e q (2*R+1) x)} < 2*W.cost (fixedWindowCost F H D)+ε ∧
          LawClose (μ.map (word e q l)) (Measure.pi (fun _ : Fin l => finiteWeightLaw β)) ε ∧
          μ.real {x | G (word e q M (integerIterate e s x))≠p x} < ε := by
  have hR0 : (0 : ℝ)≤R := Nat.cast_nonneg R
  have hl0 : (0 : ℝ)≤l := Nat.cast_nonneg l
  let θ := ε/(100*((R : ℝ)+(l : ℝ)+3))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθeq : 100*((R : ℝ)+(l : ℝ)+3)*θ=ε := by dsimp [θ]; field_simp
  have hθ0 : 0≤θ := hθ.le
  obtain ⟨K,r,m,hK,hr,hm,hcopy⟩ := synchronized_cost_producer μ e he.toMeasurePreserving htotal
    p hp β hβ hβsum hβentropy hrate zero one hθ
  obtain ⟨Z,hZ⟩ := exists_nat_gt (max ((2*R : ℕ) : ℝ) (max (l : ℝ) (100*((l : ℝ)+2*R)/ε))+1)
  refine ⟨K,r,m,hK,hr,hm,?_⟩
  filter_upwards [hcopy,eventually_ge_atTop Z] with n hn hnZ
  obtain ⟨hnpos,hrN,htail,hres,hc⟩ := hn
  have hN : 0 < n*K*m+n*m := lt_trans hr hrN
  have hNreal : (0 : ℝ) < (n*K*m+n*m : ℕ) := Nat.cast_pos.mpr hN
  have hnK : n≤n*K*m := (Nat.le_mul_of_pos_right n hK).trans (Nat.le_mul_of_pos_right (n*K) hm)
  have hnN : n≤n*K*m+n*m := hnK.trans (Nat.le_add_right _ _)
  have hZN : (Z : ℝ)≤(n*K*m+n*m : ℕ) := by exact_mod_cast hnZ.trans hnN
  have hZK : (Z : ℝ)≤(n*K*m : ℕ) := by exact_mod_cast hnZ.trans hnK
  have hRk : 2*R≤n*K*m := by
    have hh : ((2*R : ℕ) : ℝ) < (n*K*m : ℕ) := lt_of_le_of_lt (le_max_left _ _)
      ((lt_trans (lt_add_one _) hZ).trans_le hZK)
    exact_mod_cast hh.le
  have hlN : l < n*K*m+n*m := by
    have hh : (l : ℝ) < (n*K*m+n*m : ℕ) := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _))
      ((lt_trans (lt_add_one _) hZ).trans_le hZN)
    exact_mod_cast hh
  have hfrac : ((l : ℝ)+2*R)/(n*K*m+n*m : ℕ) < ε/100 := by
    apply (div_lt_iff₀ hNreal).mpr
    have hh : 100*((l : ℝ)+2*R)/ε < (n*K*m+n*m : ℕ) :=
      lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _))
        ((lt_trans (lt_add_one _) hZ).trans_le hZN)
    have hh' := (div_lt_iff₀ hε).mp hh
    nlinarith
  have hfracL : (l : ℝ)/(n*K*m+n*m : ℕ) < ε/100 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_right (by linarith only [hR0,hl0]) hNreal.le) hfrac
  have hfracR : (2*(R : ℝ))/(n*K*m+n*m : ℕ) < ε/100 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_right (by linarith only [hR0,hl0]) hNreal.le) hfrac
  refine ⟨hnpos,?_⟩
  intro W
  obtain ⟨E,V,hE,hV⟩ := hc W (fixedWindowCost F H D) (fixedWindowCost_nonneg F H D)
    (fixedWindowCost_le_one hN F H D)
    (((2*R+2 : ℕ) : ℝ)*(Marker.reserved (n*K*m+n*m) r).card/(2*(n*K*m+n*m : ℕ)))
    (fun a b => fixedWindowCost_markWord F H D a b r zero one)
  have hmarkbudget : ((2*R+2 : ℕ) : ℝ)*(Marker.reserved (n*K*m+n*m) r).card/(2*(n*K*m+n*m : ℕ))≤((R : ℝ)+1)*θ := by
    have hh := mul_le_mul_of_nonneg_left hres.le (by positivity : (0 : ℝ)≤(R : ℝ)+1)
    have heq : ((2*R+2 : ℕ) : ℝ)*(Marker.reserved (n*K*m+n*m) r).card/(2*(n*K*m+n*m : ℕ))=
        ((R : ℝ)+1)*((Marker.reserved (n*K*m+n*m) r).card/(n*K*m+n*m : ℕ)) := by
      have h2 : ((2*R+2 : ℕ) : ℝ)=2*((R : ℝ)+1) := by push_cast; ring
      rw [h2]
      field_simp
    rwa [heq]
  have hVcost : V.cost (fixedWindowCost F H D) < W.cost (fixedWindowCost F H D)+((R : ℝ)+2)*θ  := by linarith only [hV,hmarkbudget]
  obtain ⟨U,q,hU,hUp,hq,hd,hcover,hbase,hcost,_hoff,hdecode⟩ := lift_cost_transport μ e he hN hrN p hp F _ V
    (fixedWindowCost F H D) (fixedWindowCost_nonneg F H D) (fixedWindowCost_le_one hN F H D)
    zero one h01 (marked_pushWeight_support _ hr hrN zero one) E (Classical.arbitrary C) hθ
  let I := ∫ x in U,fixedWindowCost F H D (word e p (n*K*m) x) (word e q (n*K*m+n*m) x) ∂μ
  have hI : 2*(n*K*m+n*m : ℕ)*I≤2*(V.cost (fixedWindowCost F H D)+θ) := by
    have hmass := tower_real_mass_le_one μ e he.toMeasurePreserving hU (n*K*m+n*m) hd
    have hc0 := V.cost_nonneg (fixedWindowCost F H D) (fixedWindowCost_nonneg F H D)
    have hh := mul_le_mul_of_nonneg_right hmass (show 0≤V.cost (fixedWindowCost F H D)+θ by linarith)
    have hh' := mul_le_mul_of_nonneg_left hcost hNreal.le
    dsimp [I]
    nlinarith only [hh,hh']
  obtain ⟨hpaint,hfixed⟩ := fixed_window_tower_bounds μ e he.toMeasurePreserving hU hN hRk hd p q hp hq F H D
  let G := Marker.decodeWindow hN hrN zero one (extendPrefixDecoder E (Classical.arbitrary C))
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  let ν := Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)
  have hmap : ∀ w,mass (μ.restrict U) (word e q (n*K*m+n*m)) w=
      μ.real U*pushWeight (mass ν (word iidShift (fun z : ℤ → A => z 0) (n*K*m+n*m))) (Marker.markWord r zero one) w := by
    intro w
    simpa only [ν,funext (iid_word_mass β hβ hβsum (n*K*m+n*m))] using hbase w
  have hLaw := marked_tower_short_word_lawClose μ ν e he.toMeasurePreserving iidShift (iidShift_preserving _)
    hU hUp q (fun z : ℤ → A => z 0) hq (measurable_pi_apply 0) hlN hd zero one hmap hcover
  have hLaw' : LawClose (μ.map (word e q l)) (Measure.pi (fun _ : Fin l => finiteWeightLaw β))
      (θ+(l : ℝ)/(n*K*m+n*m : ℕ)+(l : ℝ)*(Marker.reserved (n*K*m+n*m) r).card/(n*K*m+n*m : ℕ)) := by
    simpa only [ν,iid_word_law] using hLaw
  refine ⟨q,-((n*K*m+n*m : ℕ) : ℤ),2*(n*K*m+n*m),G,hq,?_,?_,?_,?_⟩
  · change _≤_+_+2*(n*K*m+n*m : ℕ)*I at hpaint
    nlinarith only [hpaint,hcover,htail,hI,hVcost,hθeq,hθ,hR0,hl0]
  · have hsplit : ((n*m+2*R : ℕ) : ℝ)/(n*K*m+n*m : ℕ)=
        ((n*m : ℕ) : ℝ)/(n*K*m+n*m : ℕ)+2*(R : ℝ)/(n*K*m+n*m : ℕ) := by push_cast; ring
    rw [hsplit] at hfixed
    change _≤_+_+2*(n*K*m+n*m : ℕ)*I at hfixed
    nlinarith only [hfixed,hcover,htail,hI,hVcost,hfracR,hθeq,hθ,hR0,hl0]
  · apply hLaw'.mono
    have hres' := mul_le_mul_of_nonneg_left hres.le (Nat.cast_nonneg l)
    rw [←mul_div_assoc] at hres'
    nlinarith only [hres',hfracL,hθeq,hθ,hR0,hl0]
  · change μ.real {x | Marker.decodeWindow _ _ zero one _ (word e q (2*(n*K*m+n*m))
        (integerIterate e (-((n*K*m+n*m : ℕ) : ℤ)) x))≠p x} < ε
    nlinarith only [hdecode,hE,htail,hθeq,hθ,hR0,hl0]
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A B C : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
  [MeasurableSpace C] [Fintype C] [DecidableEq C] [MeasurableSingletonClass C] [Nonempty C]

theorem actual_fixed_window_rate_copy_q44_oai (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (p : X → C) (hp : Measurable p) (F : C → A) (H : C → B)
    (R : ℕ) (D : (Fin (2*R+1) → A) → B)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) (hrate : rate μ e p≤weightEntropy β)
    (zero one : A) (h01 : zero≠one) (l : ℕ) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ K r m : ℕ,0 < K ∧ 0 < r ∧ 0 < m ∧ ∀ᶠ n : ℕ in atTop,
      0 < n ∧ ∀ W : MatrixCoupling (mass μ (word e p (n*K*m))) (productWordWeight β (n*K*m+n*m)),
        ∃ q : X → A,Measurable q ∧
          μ.real {x | F (p x)≠q x} < 2*W.cost (fixedWindowCost F H D)+ε ∧
          μ.real {x | H (p (e^[R] x))≠D (word e q (2*R+1) x)} < 2*W.cost (fixedWindowCost F H D)+ε ∧
          LawClose (μ.map (word e q l)) (Measure.pi (fun _ : Fin l => finiteWeightLaw β)) ε ∧
          rate μ e p-ρ < rate μ e q := by
  obtain ⟨η,hη,hsmall⟩ := rate_lower_of_small_window_error (B:=A) μ e he.toMeasurePreserving p hp hρ
  obtain ⟨K,r,m,hK,hr,hm,hn⟩ := actual_fixed_window_copy μ e he htotal p hp F H R D β hβ hβsum
    hβentropy hrate zero one h01 l (lt_min hε hη)
  refine ⟨K,r,m,hK,hr,hm,?_⟩
  filter_upwards [hn] with n hn
  refine ⟨hn.1,?_⟩
  intro W
  obtain ⟨q,s,M,G,hq,hpaint,hfixed,hlaw,hdecode⟩ := hn.2 W
  have heq : mass μ (errorObs p (G ∘ word e q M ∘ integerIterate e s)) true=
      μ.real {x | G (word e q M (integerIterate e s x))≠p x} := by
    simp only [mass,Measure.real]
    congr 2
    ext x
    simp only [mem_preimage,mem_singleton_iff,errorObs,decide_eq_true_eq,
      mem_ofPred_eq,Function.comp_apply]
    exact ne_comm
  refine ⟨q,hq,lt_of_lt_of_le hpaint (add_le_add_right (min_le_left _ _) _),
    lt_of_lt_of_le hfixed (add_le_add_right (min_le_left _ _) _),hlaw.mono (min_le_left _ _),?_⟩
  apply hsmall q hq s M G
  rw [heq]
  exact hdecode.trans_le (min_le_right _ _)
end HyperbolicCoding

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.HyperbolicCoding.actual_fixed_window_rate_copy_q44_oai.{u_1, u_2, u_3, u_4} := @OAI.HyperbolicCoding.actual_fixed_window_rate_copy_q44_oai.{u_1, u_2, u_3, u_4}
