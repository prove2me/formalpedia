-- Prove2me | solution 1 for OAI.DirectionalTransience.gaussian_renewal_path_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:54:20.775716+00:00
-- url     : https://prove2.me/submissions/72fe277a-7956-496a-99ed-31aa00b2689d

import Mathlib
import Definitions.Def_OAIQ242Bal002
import Definitions.Def_OAIQ242Bal003

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordTemplate
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma independent_past_current {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) (W : ℕ → Ω → β) (hW : ∀ i, Measurable (W i))
    (hInd : iIndepFun W μ) (i : ℕ) :
    IndepFun (fun x => fun j : Fin i => W j x) (W i) μ := by
  have hd : Disjoint (Finset.range i) {i} := by simp
  have hh := hInd.indepFun_finset (Finset.range i) {i} hd hW
  have hc := hh.comp
    (show Measurable (fun f : (j : ↑(Finset.range i)) → β =>
      fun j : Fin i => f ⟨j, Finset.mem_range.mpr j.2⟩) by fun_prop)
    (show Measurable (fun f : (j : ↑({i} : Finset ℕ)) → β =>
      f ⟨i, Finset.mem_singleton.mpr rfl⟩) by fun_prop)
  exact hc

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWordIncrement
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma integrable_truncated_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S) (r : ℝ) :
    Integrable (fun x => min ((S x)^2) (r^2)) μ := by
  apply (integrable_const (r^2)).mono' ((hS.pow_const 2).min measurable_const).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (le_min (sq_nonneg _) (sq_nonneg _))]
    exact min_le_right _ _

lemma truncatedVariance_pos {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) {r : ℝ} (hr : 0 < r) :
    0 < truncatedVariance μ S r := by
  apply (integral_pos_iff_support_of_nonneg (fun x => le_min (sq_nonneg _) (sq_nonneg _))
    (integrable_truncated_square μ S hS r)).mpr
  apply hne.trans_le (measure_mono _)
  intro x hx
  exact ne_of_gt (lt_min (sq_pos_of_ne_zero hx) (sq_pos_of_pos hr))

lemma min_sq_le_mul_abs {s r : ℝ} (hr : 0 ≤ r) : min (s^2) (r^2) ≤ r*|s| := by
  by_cases hs : |s| ≤ r
  · apply (min_le_left _ _).trans
    nlinarith [sq_abs s,abs_nonneg s]
  · apply (min_le_right _ _).trans
    nlinarith [lt_of_not_ge hs]

lemma truncatedVariance_le_firstMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) {r : ℝ} (hr : 0 ≤ r) :
    truncatedVariance μ S r ≤ r*(∫ x, |S x| ∂μ) := by
  rw [truncatedVariance,← integral_const_mul]
  apply integral_mono (integrable_truncated_square μ S hS r) (hI.abs.const_mul r)
  exact fun _ => min_sq_le_mul_abs hr

lemma integral_abs_pos_of_nonzero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (hI : Integrable S μ) (hne : 0 < μ {x | S x ≠ 0}) :
    0 < ∫ x, |S x| ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun x => abs_nonneg _) hI.abs).mpr
  simpa only [Function.support,ne_eq,abs_eq_zero] using hne

lemma fluctuationScale_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) (hne : 0 < μ {x | S x ≠ 0}) {r : ℝ} (hr : 0 < r) :
    r/(∫ x, |S x| ∂μ) ≤ fluctuationScale μ S r := by
  have hM := integral_abs_pos_of_nonzero μ S hI hne
  rw [fluctuationScale,div_le_div_iff₀ hM (truncatedVariance_pos μ S hS hne hr)]
  calc
    r * truncatedVariance μ S r ≤ r*(r * ∫ x, |S x| ∂μ) :=
      mul_le_mul_of_nonneg_left (truncatedVariance_le_firstMoment μ S hS hI hr.le) hr.le
    _ = r^2*(∫ x, |S x| ∂μ) := by ring

lemma fluctuationScale_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) (hne : 0 < μ {x | S x ≠ 0}) :
    Tendsto (fluctuationScale μ S) atTop atTop := by
  apply tendsto_atTop_mono' atTop _
    (tendsto_id.atTop_div_const (integral_abs_pos_of_nonzero μ S hI hne))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact fluctuationScale_lower μ S hS hI hne hr

lemma realPartialSum_succ (X : ℕ → ℝ) (n : ℕ) :
    realPartialSum X (n+1) = realPartialSum X n+X n := by simp [realPartialSum,Finset.sum_range_succ]

lemma partialSumMax_nonneg (X : ℕ → ℝ) (n : ℕ) : 0 ≤ partialSumMax X n := by
  induction n with
  | zero => rfl
  | succ n _ => exact (abs_nonneg _).trans (le_max_right _ _)

lemma abs_partialSum_le_max (X : ℕ → ℝ) (n : ℕ) : |realPartialSum X n| ≤ partialSumMax X n := by
  cases n with
  | zero => simp [realPartialSum,partialSumMax]
  | succ n => exact le_max_right _ _

lemma partialSumMax_mono (X : ℕ → ℝ) : Monotone (partialSumMax X) :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

lemma partialSumMax_bound (X : ℕ → ℝ) {z : ℝ} (hz : 0 ≤ z) (hX : ∀ k, |X k| ≤ z) (n : ℕ) :
    partialSumMax X n ≤ n*z := by
  induction n with
  | zero => simp [partialSumMax]
  | succ n ih =>
    apply max_le
    · simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using ih.trans (le_add_of_nonneg_right hz)
    · rw [realPartialSum_succ]
      calc
        |realPartialSum X n+X n| ≤ |realPartialSum X n|+|X n| := abs_add_le _ _
        _ ≤ n*z+z := add_le_add ((abs_partialSum_le_max X n).trans ih) (hX n)
        _ = (n+1:ℕ)*z := by push_cast <;> ring

lemma abs_absSlope (t : ℝ) : |absSlope t| = 1 := by
  unfold absSlope
  split <;> simp

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SymmetricTruncate
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma abs_supporting (t x : ℝ) : absSlope t*x ≤ |t+x|-|t| := by
  by_cases ht : 0 ≤ t
  · rw [absSlope,ite_eq_left ht,one_mul,abs_of_nonneg ht]
    linarith [le_abs_self (t+x)]
  · rw [absSlope,ite_eq_right ht,neg_one_mul,abs_of_neg (lt_of_not_ge ht)]
    linarith [neg_le_abs (t+x)]

lemma measurable_realPartialSum {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (n : ℕ) : Measurable (fun ω => realPartialSum (fun k => X k ω) n) := by
  unfold realPartialSum
  fun_prop

lemma measurable_partialSumMax {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (n : ℕ) : Measurable (fun ω => partialSumMax (fun k => X k ω) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.max (measurable_realPartialSum X hX (n+1)).abs

lemma measurable_absSlope : Measurable absSlope :=
  Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const

lemma integrable_of_abs_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ ω, |f ω| ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf.aestronglyMeasurable (Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using hC ω)

lemma realPartialSum_congr {X Y : ℕ → ℝ} (n : ℕ) (hXY : ∀ k < n, X k = Y k) :
    realPartialSum X n = realPartialSum Y n := by
  exact Finset.sum_congr rfl fun k hk => hXY k (Finset.mem_range.mp hk)

lemma partialSumMax_congr {X Y : ℕ → ℝ} (n : ℕ) (hXY : ∀ k < n, X k = Y k) :
    partialSumMax X n = partialSumMax Y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [partialSumMax,partialSumMax,ih (fun k hk => hXY k (hk.trans (Nat.lt_succ_self _))),
      realPartialSum_congr (n+1) hXY]

lemma independent_max_transform {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ) (n : ℕ) :
    IndepFun (fun ω => partialSumMax (fun k => X k ω) n*absSlope (realPartialSum (fun k => X k ω) n))
      (X n) μ := by
  let Y (v : Fin n → ℝ) (k : ℕ) := if h : k < n then v ⟨k,h⟩ else 0
  have hY : ∀ k, Measurable (fun v => Y v k) := by
    intro k
    by_cases h : k < n <;> simp only [Y,h,↓reduceDIte] <;> fun_prop
  have hm : Measurable (fun v => partialSumMax (Y v) n*absSlope (realPartialSum (Y v) n)) :=
    (measurable_partialSumMax (fun k v => Y v k) hY n).mul
      (measurable_absSlope.comp (measurable_realPartialSum (fun k v => Y v k) hY n))
  have hh := (independent_past_current μ X hX hind n).comp hm measurable_id
  convert hh using 1
  · funext ω
    have heq : ∀ k < n, X k ω = Y (fun j : Fin n => X j ω) k := fun k hk => by simp [Y,hk]
    rw [partialSumMax_congr n heq,realPartialSum_congr n heq]
    rfl
  · rfl

lemma integral_partialSum_square_eq_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {z : ℝ} (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (realPartialSum (fun k => X k ω) n)^2 ∂μ) =
      ∑ k ∈ Finset.range n, ∫ ω, (X k ω)^2 ∂μ := by
  have hLp (k : ℕ) : MemLp (X k) 2 μ := MemLp.of_bound (hX k).aestronglyMeasurable z
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbound k ω)
  have hI (k : ℕ) : Integrable (X k) μ := (hLp k).integrable (by norm_num)
  have hsum : ∫ ω, realPartialSum (fun k => X k ω) n ∂μ = 0 := by
    rw [show (fun ω => realPartialSum (fun k => X k ω) n) =
      (fun ω => ∑ k ∈ Finset.range n, X k ω) from rfl,
      integral_finsetSum _ (fun k _ => hI k)]
    simp only [hmean,Finset.sum_const_zero]
  have hv := IndepFun.variance_sum (s := Finset.range n) (fun k _ => hLp k)
    (fun i _ j _ hij => hind.indepFun hij)
  have heq : (∑ k ∈ Finset.range n, X k) = (fun ω => realPartialSum (fun k => X k ω) n) := by
    ext ω
    simp only [realPartialSum,Finset.sum_apply]
  rw [heq,variance_eq_integral (measurable_realPartialSum X hX n).aemeasurable,hsum] at hv
  simpa only [variance_eq_integral (hX _).aemeasurable,hmean,sub_zero] using hv

lemma measurable_symmetricTruncate (z : ℝ) : Measurable (symmetricTruncate z) :=
  Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_id measurable_const

lemma symmetricTruncate_bound {z : ℝ} (hz : 0 ≤ z) (x : ℝ) : |symmetricTruncate z x| ≤ z := by
  unfold symmetricTruncate
  split_ifs with h
  · exact h
  · simpa using hz

lemma symmetricTruncate_neg (z x : ℝ) : symmetricTruncate z (-x) = -symmetricTruncate z x := by
  simp only [symmetricTruncate,abs_neg]
  split_ifs <;> simp

lemma symmetricTruncate_sq_le (z x : ℝ) : (symmetricTruncate z x)^2 ≤ min (x^2) (z^2) := by
  unfold symmetricTruncate
  split_ifs with h
  · exact le_min le_rfl (by nlinarith [abs_nonneg x,sq_abs x])
  · simpa only [zero_pow (by norm_num : 2 ≠ 0)] using le_min (sq_nonneg x) (sq_nonneg z)

lemma integral_symmetricTruncate_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (z : ℝ)
    (hsym : IdentDistrib S (fun ω => -S ω) μ μ) :
    (∫ ω, symmetricTruncate z (S ω) ∂μ) = 0 := by
  have he := (hsym.comp (measurable_symmetricTruncate z)).integral_eq
  simp only [Function.comp_apply,symmetricTruncate_neg,integral_neg] at he
  linarith

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IntegerMedian
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma one_sub_cos_sinc (x : ℝ) :
    1-Real.cos x = x^2/2*(Real.sinc (x/2))^2 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero (div_ne_zero hx (by norm_num))]
    have hc := Real.cos_two_mul (x/2)
    have hs := Real.sin_sq_add_cos_sq (x/2)
    have he : 2*(x/2) = x := by ring
    rw [he] at hc
    field_simp
    nlinarith

lemma cosine_quadratic_local (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ y : ℝ, |y| ≤ δ →
      |(1-Real.cos (t*y)) - (t^2/2)*y^2| ≤ ε*y^2 := by
  let c : ℝ → ℝ := fun y => t^2/2*((Real.sinc (t*y/2))^2-1)
  have hc : Continuous c := by fun_prop
  have hc0 : c 0 = 0 := by simp [c]
  obtain ⟨δ,hδ,hd⟩ := (Metric.continuousAt_iff.mp hc.continuousAt) ε hε
  refine ⟨min (δ/2) 1,lt_min (by positivity) zero_lt_one,min_le_right ..,?_⟩
  intro y hy
  have hyd : dist y 0 < δ := by
    rw [Real.dist_eq,sub_zero]
    exact lt_of_le_of_lt (hy.trans (min_le_left ..)) (by linarith)
  have hcy : |c y| < ε := by simpa [Real.dist_eq,hc0] using hd hyd
  have he : (1-Real.cos (t*y)) - (t^2/2)*y^2 = c y*y^2 := by
    rw [one_sub_cos_sinc]
    dsimp [c]
    ring
  rw [he,abs_mul,abs_of_nonneg (sq_nonneg y)]
  exact mul_le_mul_of_nonneg_right hcy.le (sq_nonneg y)

lemma truncatedVariance_div {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) {r : ℝ} (hr : 0 < r) :
    truncatedVariance μ (fun x => S x/r) 1 = truncatedVariance μ S r / r^2 := by
  unfold truncatedVariance
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [one_pow,div_pow,← min_div_div_right (le_of_lt (sq_pos_of_pos hr)),div_self (pow_ne_zero 2 (ne_of_gt hr))]

lemma gaussian_quadratic_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) (r : ℕ → ℝ) (hr : IsGaussianSequence μ S r)
    (g : ℝ → ℝ) (hg : Measurable g) (c C : ℝ) (hC : ∀ y, |g y| ≤ C)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ y, |y| ≤ δ → |g y-c*y^2| ≤ ε*y^2) :
    Tendsto (fun i => fluctuationScale μ S (r i) * ∫ x, g (S x/r i) ∂μ)
      atTop (𝓝 c) := by
  have hC0 : 0 ≤ C := (abs_nonneg (g 0)).trans (hC 0)
  have hIg (i : ℕ) : Integrable (fun x => g (S x/r i)) μ :=
    (integrable_const C).mono' ((hg.comp (hS.div_const _)).aestronglyMeasurable)
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC (S x/r i))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδ1,hlocal⟩ := hc (ε/2) (by positivity)
  have htail : Tendsto (fun i => (C+|c|) *
      (fluctuationScale μ S (r i) * μ.real {x | δ*r i < |S x|})) atTop (𝓝 0) := by
    simpa using (hr.2 δ hδ).const_mul (C+|c|)
  have ht := (tendsto_order.mp htail).2 (ε/2) (by positivity)
  filter_upwards [hr.1.eventually (eventually_gt_atTop (0:ℝ)),ht] with i hri hti
  let Y : Ω → ℝ := fun x => S x/r i
  let A : Set Ω := {x | δ*r i < |S x|}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hS.abs
  have hY : Measurable Y := hS.div_const _
  have hmt : Integrable (fun x => min ((Y x)^2) 1) μ := by
    simpa using integrable_truncated_square μ Y hY 1
  have hE : ∀ x, |g (Y x)-c*min ((Y x)^2) 1| ≤
      (ε/2)*min ((Y x)^2) 1 + A.indicator (fun _ => C+|c|) x := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      have hm0 : 0 ≤ min ((Y x)^2) 1 := le_min (sq_nonneg _) zero_le_one
      have hm1 : min ((Y x)^2) 1 ≤ 1 := min_le_right ..
      have hb := (abs_sub (g (Y x)) (c*min ((Y x)^2) 1)).trans
        (add_le_add (hC (Y x)) (le_of_eq (abs_mul c _)))
      rw [abs_of_nonneg hm0] at hb
      nlinarith [abs_nonneg c]
    · rw [Set.indicator_of_notMem hx,add_zero]
      have hxy : |Y x| ≤ δ := by
        rw [show Y x = S x/r i from rfl,abs_div,abs_of_pos hri,div_le_iff₀ hri]
        exact le_of_not_gt hx
      have hx1 : (Y x)^2 ≤ 1 := by nlinarith [sq_abs (Y x),abs_nonneg (Y x)]
      rw [min_eq_left hx1]
      exact hlocal _ hxy
  have hInt : |(∫ x, g (Y x) ∂μ)-c*truncatedVariance μ Y 1| ≤
      ε/2*truncatedVariance μ Y 1 + (C+|c|)*μ.real A := by
    simp only [truncatedVariance,one_pow]
    rw [← integral_const_mul,← integral_sub (hIg i) (hmt.const_mul c)]
    calc
      _ ≤ ∫ x, |g (Y x)-c*min ((Y x)^2) 1| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, (ε/2)*min ((Y x)^2) 1 + A.indicator (fun _ => C+|c|) x ∂μ :=
        integral_mono ((hIg i).sub (hmt.const_mul c)).abs
          ((hmt.const_mul (ε/2)).add ((integrable_const (C+|c|)).indicator hA)) hE
      _ = _ := by
        rw [integral_add (hmt.const_mul (ε/2)) ((integrable_const (C+|c|)).indicator hA),
          integral_const_mul,integral_indicator hA,integral_const]
        simp [smul_eq_mul,mul_comm,Measure.real]
  have hmpos := truncatedVariance_pos μ S hS hne hri
  have hnpos : 0 < fluctuationScale μ S (r i) := div_pos (sq_pos_of_pos hri) hmpos
  have hnorm : fluctuationScale μ S (r i)*truncatedVariance μ Y 1 = 1 := by
    rw [show Y = (fun x => S x/r i) from rfl,truncatedVariance_div μ S hri,fluctuationScale]
    field_simp
  have hbound := mul_le_mul_of_nonneg_left hInt hnpos.le
  rw [Real.dist_eq]
  have hrew : fluctuationScale μ S (r i)*( (∫ x, g (Y x) ∂μ)-c*truncatedVariance μ Y 1) =
      fluctuationScale μ S (r i)*(∫ x, g (Y x) ∂μ)-c := by
    rw [mul_sub]
    congr 1
    calc
      _ = c*(fluctuationScale μ S (r i)*truncatedVariance μ Y 1) := by ring
      _ = c := by rw [hnorm,mul_one]
  have hab : |fluctuationScale μ S (r i)*( (∫ x, g (Y x) ∂μ)-c*truncatedVariance μ Y 1)| =
      fluctuationScale μ S (r i)*|(∫ x, g (Y x) ∂μ)-c*truncatedVariance μ Y 1| := by
    rw [abs_mul,abs_of_pos hnpos]
  rw [← hab,hrew] at hbound
  have hrw : fluctuationScale μ S (r i) *
      (ε/2*truncatedVariance μ Y 1 + (C+|c|)*μ.real A) =
      ε/2+(C+|c|)*(fluctuationScale μ S (r i)*μ.real A) := by
    calc
      _ = ε/2*(fluctuationScale μ S (r i)*truncatedVariance μ Y 1) +
        (C+|c|)*(fluctuationScale μ S (r i)*μ.real A) := by ring
      _ = _ := by rw [hnorm,mul_one]
  rw [hrw] at hbound
  exact hbound.trans_lt (by linarith)

lemma gaussian_cosine_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) (r : ℕ → ℝ) (hr : IsGaussianSequence μ S r) (t : ℝ) :
    Tendsto (fun i => fluctuationScale μ S (r i) * ∫ x, 1-Real.cos (t*(S x/r i)) ∂μ)
      atTop (𝓝 (t^2/2)) := by
  apply gaussian_quadratic_integral μ S hS hne r hr
    (fun y => 1-Real.cos (t*y)) (by fun_prop) (t^2/2) 2
  · intro y
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
    linarith [Real.neg_one_le_cos (t*y)]
  · exact fun ε hε => cosine_quadratic_local t hε

lemma symmetric_sine_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (hsym : IdentDistrib S (fun x => -S x) μ μ) (t : ℝ) :
    (∫ x, Real.sin (t*S x) ∂μ) = 0 := by
  have he := (hsym.comp (u := fun y : ℝ => Real.sin (t*y)) (by fun_prop)).integral_eq
  simp only [Function.comp_def,mul_neg,Real.sin_neg,integral_neg] at he
  linarith

lemma symmetric_charFun_cosine {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hsym : IdentDistrib S (fun x => -S x) μ μ) (t : ℝ) :
    charFun (μ.map S) t = ((∫ x, Real.cos (t*S x) ∂μ : ℝ) : ℂ) := by
  have hI : Integrable (fun x => Complex.exp ((t*S x : ℝ)*Complex.I)) μ := by
    apply (integrable_const (1:ℝ)).mono' (by fun_prop)
    exact Eventually.of_forall fun x => (Complex.norm_exp_ofReal_mul_I (t*S x)).le
  rw [charFun_apply_real,integral_map hS.aemeasurable (by fun_prop)]
  simp only [← Complex.ofReal_mul]
  apply Complex.ext
  · simpa only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using (integral_re hI).symm
  · have he := (integral_im hI).symm
    simpa only [RCLike.im_to_complex, Complex.exp_ofReal_mul_I, Complex.add_im,
      Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_mul, add_zero, zero_add,
      symmetric_sine_integral μ S hsym t] using he

lemma gaussian_cosine_drift {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) (r : ℕ → ℝ) (hr : IsGaussianSequence μ S r) (t : ℝ) :
    Tendsto (fun i => fluctuationScale μ S (r i) *
      ((∫ x, Real.cos (t*(S x/r i)) ∂μ)-1)) atTop (𝓝 (-(t^2/2))) := by
  have hcos (i : ℕ) : Integrable (fun x => Real.cos (t*(S x/r i))) μ :=
    (integrable_const (1:ℝ)).mono' (by fun_prop)
      (Eventually.of_forall fun _ => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)
  convert (gaussian_cosine_limit μ S hS hne r hr t).neg using 1
  all_goals try with_reducible_and_instances rfl
  ext i
  rw [integral_sub (integrable_const 1) (hcos i),integral_const]
  simp only [probReal_univ,one_smul]
  ring

lemma tendsto_pow_variable_of_drift {a : ℕ → ℝ} {k : ℕ → ℕ} {c : ℝ}
    (ha : Tendsto a atTop (𝓝 1))
    (hd : Tendsto (fun i => (k i : ℝ)*(a i-1)) atTop (𝓝 c)) :
    Tendsto (fun i => (a i)^(k i)) atTop (𝓝 (Real.exp c)) := by
  have hds : Tendsto (fun i => dslope Real.log 1 (a i)) atTop (𝓝 1) := by
    have h := (continuousAt_dslope_same.mpr (Real.differentiableAt_log one_ne_zero)).tendsto.comp ha
    simpa [Real.deriv_log,Function.comp_def] using h
  have hlog : Tendsto (fun i => (k i : ℝ)*Real.log (a i)) atTop (𝓝 c) := by
    convert hd.mul hds using 1
    · ext i
      have he := sub_smul_dslope Real.log 1 (a i)
      simp only [smul_eq_mul,Real.log_one,sub_zero] at he
      rw [mul_assoc,he]
    · simp
  apply (Real.continuous_exp.tendsto c |>.comp hlog).congr'
  filter_upwards [(tendsto_order.mp ha).1 0 zero_lt_one] with i hi
  dsimp only [Function.comp_def]
  rw [Real.exp_nat_mul,Real.exp_log hi]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_SignedHeight
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma max_fourth_increment {m a : ℝ} :
    (max m |a|)^4-m^4 ≤ 2*|a| *((max m |a|)^3-m^3) := by
  by_cases h : |a| ≤ m
  · rw [max_eq_left h]; ring_nf; rfl
  · rw [max_eq_right (le_of_not_ge h)]
    have hp := mul_nonneg (mul_nonneg (abs_nonneg a) (sq_nonneg m))
      (sub_nonneg.mpr (le_of_not_ge h))
    nlinarith [sq_nonneg (|a|^2-m^2)]

lemma partialSumMax_fourth_pathwise (X : ℕ → ℝ) (n : ℕ) :
    (partialSumMax X n)^4 ≤ 2*(partialSumMax X n)^3*|realPartialSum X n|-
      2*∑ k ∈ Finset.range n, (partialSumMax X k)^3*absSlope (realPartialSum X k)*X k := by
  induction n with
  | zero => simp [partialSumMax]
  | succ n ih =>
    have hincr := max_fourth_increment (m := partialSumMax X n)
      (a := realPartialSum X (n+1))
    have hs := mul_le_mul_of_nonneg_left (abs_supporting (realPartialSum X n) (X n))
      (pow_nonneg (partialSumMax_nonneg X n) 3)
    rw [← realPartialSum_succ] at hs
    rw [Finset.sum_range_succ]
    change (max (partialSumMax X n) |realPartialSum X (n+1)|)^4 ≤ _
    change _ ≤ 2*(max (partialSumMax X n) |realPartialSum X (n+1)|)^3 * |realPartialSum X (n+1)|-_
    nlinarith

lemma partialSumMax_fourth_pathwise_bound (X : ℕ → ℝ) (n : ℕ) :
    (partialSumMax X n)^4 ≤ 32*(realPartialSum X n)^4-
      4*∑ k ∈ Finset.range n, (partialSumMax X k)^3*absSlope (realPartialSum X k)*X k := by
  have h := partialSumMax_fourth_pathwise X n
  have hy : 2*(partialSumMax X n)^3*|realPartialSum X n| ≤
      (partialSumMax X n)^4/2+16*(realPartialSum X n)^4 := by
    nlinarith [sq_nonneg ((partialSumMax X n)^2-4*partialSumMax X n*|realPartialSum X n|),
      sq_nonneg ((partialSumMax X n)^2-8*(realPartialSum X n)^2),
      sq_abs (realPartialSum X n)]
  linarith

lemma integrable_partialSumMax_pow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n p : ℕ) :
    Integrable (fun ω => (partialSumMax (fun k => X k ω) n)^p) μ := by
  apply integrable_of_abs_bound μ _ ((measurable_partialSumMax X hX n).pow_const p) ((n*z)^p)
  intro ω
  rw [abs_of_nonneg (pow_nonneg (partialSumMax_nonneg _ _) _)]
  exact pow_le_pow_left₀ (partialSumMax_nonneg _ _) (partialSumMax_bound _ hz (fun k => hbound k ω) n) p

lemma integrable_realPartialSum_pow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n p : ℕ) :
    Integrable (fun ω => (realPartialSum (fun k => X k ω) n)^p) μ := by
  apply integrable_of_abs_bound μ _ ((measurable_realPartialSum X hX n).pow_const p) ((n*z)^p)
  intro ω
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) ((abs_partialSum_le_max _ _).trans
    (partialSumMax_bound _ hz (fun k => hbound k ω) n)) p

lemma absSlope_cube (t : ℝ) : (absSlope t)^3 = absSlope t := by
  unfold absSlope
  split <;> norm_num

lemma independent_max_cube_transform {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ) (n : ℕ) :
    IndepFun (fun ω => (partialSumMax (fun k => X k ω) n)^3*absSlope (realPartialSum (fun k => X k ω) n))
      (X n) μ := by
  have hh := (independent_max_transform μ X hX hind n).comp
    (show Measurable (fun x : ℝ => x^3) by fun_prop) measurable_id
  simpa only [Function.comp_def,mul_pow,absSlope_cube,id_eq] using hh

lemma integral_partialSumMax_fourth_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (partialSumMax (fun k => X k ω) n)^4 ∂μ) ≤
      32*∫ ω, (realPartialSum (fun k => X k ω) n)^4 ∂μ := by
  let C (k : ℕ) (ω : Ω) := (partialSumMax (fun j => X j ω) k)^3*absSlope (realPartialSum (fun j => X j ω) k)
  have hC (k : ℕ) : Measurable (C k) := ((measurable_partialSumMax X hX k).pow_const 3).mul
    (measurable_absSlope.comp (measurable_realPartialSum X hX k))
  have hCI (k : ℕ) : Integrable (fun ω => C k ω*X k ω) μ := by
    apply integrable_of_abs_bound μ _ ((hC k).mul (hX k)) ((k*z)^3*z)
    intro ω
    dsimp [C]
    rw [abs_mul,abs_mul,abs_absSlope,mul_one,abs_of_nonneg (pow_nonneg (partialSumMax_nonneg _ _) _)]
    exact mul_le_mul (pow_le_pow_left₀ (partialSumMax_nonneg _ _)
      (partialSumMax_bound _ hz (fun j => hbound j ω) k) 3) (hbound k ω)
      (abs_nonneg _) (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hz) 3)
  have hzero (k : ℕ) : ∫ ω, C k ω*X k ω ∂μ = 0 := by
    rw [(independent_max_cube_transform μ X hX hind k).integral_fun_mul_eq_mul_integral
      (hC k).aestronglyMeasurable (hX k).aestronglyMeasurable,hmean,mul_zero]
  have hm := integral_mono (integrable_partialSumMax_pow μ X hX hz hbound n 4)
    (((integrable_realPartialSum_pow μ X hX hz hbound n 4).const_mul 32).sub
      ((integrable_finsetSum (Finset.range n) (fun k _ => hCI k)).const_mul 4))
    (fun ω => partialSumMax_fourth_pathwise_bound (fun k => X k ω) n)
  simp only [Pi.sub_apply] at hm
  rw [integral_sub ((integrable_realPartialSum_pow μ X hX hz hbound n 4).const_mul 32)
    ((integrable_finsetSum (Finset.range n) (fun k _ => hCI k)).const_mul 4),
    integral_const_mul,integral_const_mul,integral_finsetSum _ (fun k _ => hCI k)] at hm
  simpa only [hzero,Finset.sum_const_zero,mul_zero,sub_zero] using hm

lemma independent_partialSum_current {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ) (n : ℕ) :
    IndepFun (fun ω => realPartialSum (fun k => X k ω) n) (X n) μ := by
  have hh := (independent_past_current μ X hX hind n).comp
    (show Measurable (fun v : Fin n → ℝ => ∑ k, v k) by fun_prop) measurable_id
  convert hh using 1
  · funext ω
    exact (Fin.sum_univ_eq_sum_range (fun k => X k ω) n).symm
  · rfl

lemma integrable_pow_mul_of_abs_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F G : Ω → ℝ)
    (hF : Measurable F) (hG : Measurable G) {a b : ℝ}
    (ha : ∀ ω, |F ω| ≤ a) (hb : ∀ ω, |G ω| ≤ b) (p q : ℕ) :
    Integrable (fun ω => F ω^p*G ω^q) μ := by
  apply integrable_of_abs_bound μ _ (by fun_prop) (a^p*b^q)
  intro ω
  rw [abs_mul,abs_pow,abs_pow]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (ha ω) p)
    (pow_le_pow_left₀ (abs_nonneg _) (hb ω) q) (pow_nonneg (abs_nonneg _) _)
    (pow_nonneg ((abs_nonneg (F ω)).trans (ha ω)) _)

lemma integral_independent_add_fourth {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F G : Ω → ℝ)
    (hF : Measurable F) (hG : Measurable G) (hind : IndepFun F G μ)
    (hmF : ∫ ω, F ω ∂μ = 0) (hmG : ∫ ω, G ω ∂μ = 0)
    {a b : ℝ} (ha : ∀ ω, |F ω| ≤ a) (hb : ∀ ω, |G ω| ≤ b) :
    (∫ ω, (F ω+G ω)^4 ∂μ) =
      (∫ ω, F ω^4 ∂μ)+6*(∫ ω, F ω^2 ∂μ)*(∫ ω, G ω^2 ∂μ)+(∫ ω, G ω^4 ∂μ) := by
  have hI := integrable_pow_mul_of_abs_bound μ F G hF hG ha hb
  have hF4 : Integrable (fun ω => F ω^4) μ := by simpa using hI 4 0
  have hG4 : Integrable (fun ω => G ω^4) μ := by simpa using hI 0 4
  have h31 : Integrable (fun ω => 4*(F ω^3*G ω^1)) μ := (hI 3 1).const_mul 4
  have h22 : Integrable (fun ω => 6*(F ω^2*G ω^2)) μ := (hI 2 2).const_mul 6
  have h13 : Integrable (fun ω => 4*(F ω^1*G ω^3)) μ := (hI 1 3).const_mul 4
  have hfactor (p q : ℕ) : (∫ ω, F ω^p*G ω^q ∂μ) =
      (∫ ω, F ω^p ∂μ)*(∫ ω, G ω^q ∂μ) :=
    (hind.comp (by fun_prop : Measurable (fun x : ℝ => x^p))
      (by fun_prop : Measurable (fun x : ℝ => x^q))).integral_fun_mul_eq_mul_integral
      (hF.pow_const p).aestronglyMeasurable (hG.pow_const q).aestronglyMeasurable
  have heq : (fun ω => (F ω+G ω)^4) =
      (fun ω => F ω^4+4*(F ω^3*G ω^1)+6*(F ω^2*G ω^2)+4*(F ω^1*G ω^3)+G ω^4) := by
    ext ω; ring
  have h12 : Integrable (fun ω => F ω^4+4*(F ω^3*G ω^1)) μ := hF4.add h31
  have h123 : Integrable (fun ω => F ω^4+4*(F ω^3*G ω^1)+6*(F ω^2*G ω^2)) μ := h12.add h22
  have h1234 : Integrable (fun ω => F ω^4+4*(F ω^3*G ω^1)+6*(F ω^2*G ω^2)+4*(F ω^1*G ω^3)) μ := h123.add h13
  rw [heq,integral_add h1234 hG4,integral_add h123 h13,integral_add h12 h22,
    integral_add hF4 h31]
  simp only [integral_const_mul]
  rw [hfactor 3 1,hfactor 2 2,hfactor 1 3]
  simp only [pow_one,hmF,hmG,mul_zero,zero_mul,add_zero]
  ring

lemma integral_iid_partialSum_fourth_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (realPartialSum (fun k => X k ω) n)^4 ∂μ) ≤
      n*(∫ ω, (X 0 ω)^4 ∂μ)+3*(n:ℝ)^2*(∫ ω, (X 0 ω)^2 ∂μ)^2 := by
  have hmeans (k : ℕ) : ∫ ω, X k ω ∂μ = 0 := (hident k).integral_eq.trans hmean
  have hpows (k p : ℕ) : (∫ ω, (X k ω)^p ∂μ) = (∫ ω, (X 0 ω)^p ∂μ) :=
    ((hident k).comp (u := fun x : ℝ => x^p) (by fun_prop)).integral_eq
  have hsq (n : ℕ) : (∫ ω, (realPartialSum (fun k => X k ω) n)^2 ∂μ) =
      n*(∫ ω, (X 0 ω)^2 ∂μ) := by
    rw [integral_partialSum_square_eq_sum μ X hX hind hmeans hbound]
    simp only [hpows,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hsummean (n : ℕ) : ∫ ω, realPartialSum (fun k => X k ω) n ∂μ = 0 := by
    rw [show (fun ω => realPartialSum (fun k => X k ω) n) =
      (fun ω => ∑ k ∈ Finset.range n, X k ω) from rfl,
      integral_finsetSum _ (fun k _ => integrable_of_abs_bound μ _ (hX k) z (hbound k))]
    simp only [hmeans,Finset.sum_const_zero]
  induction n with
  | zero => simp [realPartialSum]
  | succ n ih =>
    simp only [realPartialSum_succ]
    rw [integral_independent_add_fourth μ _ _ (measurable_realPartialSum X hX n) (hX n)
      (independent_partialSum_current μ X hX hind n) (hsummean n) (hmeans n)
      (fun ω => (abs_partialSum_le_max _ _).trans (partialSumMax_bound _ hz (fun k => hbound k ω) n))
      (hbound n),hsq]
    simp only [hpows]
    push_cast
    nlinarith [sq_nonneg (∫ ω, (X 0 ω)^2 ∂μ)]

lemma integral_iid_truncated_max_fourth_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {z r : ℝ} (hz : 0 ≤ z) (hzr : z ≤ r) (n : ℕ) :
    (∫ ω, (partialSumMax (fun k => symmetricTruncate z (X k ω)) n)^4 ∂μ) ≤
      32*(n:ℝ)*z^2*truncatedVariance μ (X 0) r+
        96*(n:ℝ)^2*(truncatedVariance μ (X 0) r)^2 := by
  let Y := fun k ω => symmetricTruncate z (X k ω)
  have hY (k : ℕ) : Measurable (Y k) := (measurable_symmetricTruncate z).comp (hX k)
  have hYb := fun k ω => symmetricTruncate_bound hz (X k ω)
  have hYi : iIndepFun Y μ := hind.comp (fun _ => symmetricTruncate z) (fun _ => measurable_symmetricTruncate z)
  have hYid (k : ℕ) : IdentDistrib (Y k) (Y 0) μ μ := (hident k).comp (measurable_symmetricTruncate z)
  have hYm : ∫ ω, Y 0 ω ∂μ = 0 := integral_symmetricTruncate_zero μ (X 0) z hsym
  have hYmeans (k : ℕ) : ∫ ω, Y k ω ∂μ = 0 := (hYid k).integral_eq.trans hYm
  have hI (p : ℕ) : Integrable (fun ω => (Y 0 ω)^p) μ := by
    apply integrable_of_abs_bound μ _ ((hY 0).pow_const p) (z^p)
    intro ω
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hYb 0 ω) p
  have hvar : (∫ ω, (Y 0 ω)^2 ∂μ) ≤ truncatedVariance μ (X 0) r := by
    apply integral_mono (hI 2) (integrable_truncated_square μ (X 0) (hX 0) r)
    intro ω
    exact (symmetricTruncate_sq_le z _).trans
      (min_le_min le_rfl (pow_le_pow_left₀ hz hzr 2))
  have hfour : (∫ ω, (Y 0 ω)^4 ∂μ) ≤ z^2*(∫ ω, (Y 0 ω)^2 ∂μ) := by
    rw [← integral_const_mul]
    apply integral_mono (hI 4) ((hI 2).const_mul (z^2))
    intro ω
    have hs : (Y 0 ω)^2 ≤ z^2 := by
      nlinarith [sq_abs (Y 0 ω),hYb 0 ω,abs_nonneg (Y 0 ω)]
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (Y 0 ω))]
  have hv0 : 0 ≤ ∫ ω, (Y 0 ω)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  calc
    _ ≤ 32*(∫ ω, (realPartialSum (fun k => Y k ω) n)^4 ∂μ) :=
      integral_partialSumMax_fourth_le μ Y hY hYi hYmeans hz hYb n
    _ ≤ 32*(n*(∫ ω, (Y 0 ω)^4 ∂μ)+3*(n:ℝ)^2*(∫ ω, (Y 0 ω)^2 ∂μ)^2) :=
      mul_le_mul_of_nonneg_left (integral_iid_partialSum_fourth_le μ Y hY hYi hYid hYm hz hYb n) (by norm_num)
    _ ≤ 32*(n*(z^2*truncatedVariance μ (X 0) r)+3*(n:ℝ)^2*(truncatedVariance μ (X 0) r)^2) := by
      gcongr
      · exact hfour.trans (mul_le_mul_of_nonneg_left hvar (sq_nonneg z))
    _ = _ := by ring

lemma measureReal_truncated_max_gt_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {z r a : ℝ} (hz : 0 ≤ z) (hzr : z ≤ r) (ha : 0 < a) (n : ℕ) :
    μ.real {ω | a < partialSumMax (fun k => symmetricTruncate z (X k ω)) n} ≤
      (32*(n:ℝ)*z^2*truncatedVariance μ (X 0) r+
        96*(n:ℝ)^2*(truncatedVariance μ (X 0) r)^2) / a^4 := by
  let Y := fun k ω => symmetricTruncate z (X k ω)
  have hY (k : ℕ) : Measurable (Y k) := (measurable_symmetricTruncate z).comp (hX k)
  have hYb := fun k ω => symmetricTruncate_bound hz (X k ω)
  have hb := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun ω => pow_nonneg (partialSumMax_nonneg (fun k => Y k ω) n) 4))
    (integrable_partialSumMax_pow μ Y hY hz hYb n 4) (a^4)
  have hmono : μ.real {ω | a < partialSumMax (fun k => Y k ω) n} ≤
      μ.real {ω | a^4 ≤ (partialSumMax (fun k => Y k ω) n)^4} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    exact pow_le_pow_left₀ ha.le hω.le 4
  apply (le_div_iff₀ (pow_pos ha 4)).mpr
  calc
    _ ≤ a^4*μ.real {ω | a^4 ≤ (partialSumMax (fun k => Y k ω) n)^4} := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hmono (pow_nonneg ha.le 4)
    _ ≤ (∫ ω, (partialSumMax (fun k => Y k ω) n)^4 ∂μ) := hb
    _ ≤ _ := integral_iid_truncated_max_fourth_le μ X hX hind hident hsym hz hzr n

lemma measureReal_iid_max_gt_fourth_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {z r a : ℝ} (hz : 0 ≤ z) (hzr : z ≤ r) (ha : 0 < a) (n : ℕ) :
    μ.real {ω | a < partialSumMax (fun k => X k ω) n} ≤
      n*μ.real {ω | z < |X 0 ω|}+
      (32*(n:ℝ)*z^2*truncatedVariance μ (X 0) r+
        96*(n:ℝ)^2*(truncatedVariance μ (X 0) r)^2) / a^4 := by
  let A : ℕ → Set Ω := fun k => {ω | z < |X k ω|}
  let B : Set Ω := {ω | a < partialSumMax (fun k => symmetricTruncate z (X k ω)) n}
  have hsub : {ω | a < partialSumMax (fun k => X k ω) n} ⊆
      (⋃ k ∈ Finset.range n, A k) ∪ B := by
    intro ω hω
    by_cases ht : ω ∈ ⋃ k ∈ Finset.range n, A k
    · exact Or.inl ht
    · right
      have hc : ∀ k < n, X k ω = symmetricTruncate z (X k ω) := by
        intro k hk
        have hnot : ¬ z < |X k ω| := fun h => ht (Set.mem_iUnion.mpr
          ⟨k,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hk,h⟩⟩)
        simp only [symmetricTruncate,ite_eq_left (le_of_not_gt hnot)]
      change a < partialSumMax (fun k => symmetricTruncate z (X k ω)) n
      rwa [← partialSumMax_congr n hc]
  have htail (k : ℕ) : μ.real (A k) = μ.real (A 0) := by
    exact congrArg ENNReal.toReal ((hident k).measure_mem_eq
      (show MeasurableSet {x : ℝ | z < |x|} from measurableSet_lt measurable_const measurable_id.abs))
  calc
    _ ≤ μ.real ((⋃ k ∈ Finset.range n, A k) ∪ B) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real (⋃ k ∈ Finset.range n, A k)+μ.real B := measureReal_union_le _ _
    _ ≤ (∑ k ∈ Finset.range n, μ.real (A k))+μ.real B :=
      add_le_add (measureReal_biUnion_finset_le _ _) le_rfl
    _ = n*μ.real {ω | z < |X 0 ω|}+μ.real B := by
      simp only [htail,Finset.sum_const,Finset.card_range,nsmul_eq_mul,A]
    _ ≤ _ := add_le_add le_rfl (measureReal_truncated_max_gt_le μ X hX hind hident hsym hz hzr ha n)

lemma gaussian_charFun_power_limit_count {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) (hne : 0 < μ {x | S x ≠ 0})
    (hsym : IdentDistrib S (fun x => -S x) μ μ) (r : ℕ → ℝ)
    (hr : IsGaussianSequence μ S r) (k : ℕ → ℕ) {τ : ℝ}
    (hk : Tendsto (fun i => (k i : ℝ)/fluctuationScale μ S (r i)) atTop (𝓝 τ)) (t : ℝ) :
    Tendsto (fun i => (charFun (μ.map S) (t/r i))^(k i))
      atTop (𝓝 (Complex.exp (-(τ*t^2/2 : ℝ)))) := by
  have hn : Tendsto (fun i => fluctuationScale μ S (r i)) atTop atTop :=
    (fluctuationScale_tendsto μ S hS hI hne).comp hr.1
  have hd := gaussian_cosine_drift μ S hS hne r hr t
  have hzero : Tendsto (fun i => (∫ x, Real.cos (t*(S x/r i)) ∂μ)-1) atTop (𝓝 0) := by
    have hz := hd.mul (tendsto_inv_atTop_zero.comp hn)
    simp only [mul_zero] at hz
    apply hz.congr'
    filter_upwards [hn.eventually (eventually_gt_atTop (0:ℝ))] with i hi
    dsimp only [Function.comp_def]
    field_simp
  have ha : Tendsto (fun i => ∫ x, Real.cos (t*(S x/r i)) ∂μ) atTop (𝓝 1) := by
    simpa using hzero.add_const 1
  have hdk : Tendsto (fun i => (k i : ℝ)*
      ((∫ x, Real.cos (t*(S x/r i)) ∂μ)-1)) atTop (𝓝 (-(τ*t^2/2))) := by
    have hc := hk.mul hd
    have he : τ * (-(t^2/2)) = -(τ*t^2/2) := by ring
    rw [he] at hc
    apply hc.congr'
    filter_upwards [hn.eventually (eventually_gt_atTop (0:ℝ))] with i hi
    field_simp
  convert (tendsto_pow_variable_of_drift ha hdk).ofReal using 1
  · ext i
    rw [symmetric_charFun_cosine μ S hS hsym, ← Complex.ofReal_pow]
    congr 2
    apply integral_congr_ae
    filter_upwards [] with x
    congr 1
    ring
  · simp

lemma charFun_independent_finite_blocks {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (k : ι → ℕ) (g : (j : ι) → Fin (k j) → ℕ)
    (hg : Function.Injective (fun p : (j : ι) × Fin (k j) => g p.1 p.2)) (r : ℝ)
    (t : EuclideanSpace ℝ ι) :
    charFun (μ.map (fun ω => WithLp.toLp 2 (fun j => (∑ l, X (g j l) ω)/r))) t =
      ∏ j, (charFun (μ.map (X 0)) (t j/r))^(k j) := by
  classical
  let Y (p : (j : ι) × Fin (k j)) (ω : Ω) := (t p.1/r)*X (g p.1 p.2) ω
  have hY p : Measurable (Y p) := (hX _).const_mul _
  have hiY : iIndepFun Y μ := (hind.precomp hg).comp
    (fun p x => (t p.1/r)*x) (fun _ => by fun_prop)
  have heq : charFun (μ.map (fun ω => WithLp.toLp 2 (fun j => (∑ l, X (g j l) ω)/r))) t =
      charFun (μ.map (fun ω => ∑ p, Y p ω)) 1 := by
    rw [charFun, charFun, integral_map (by fun_prop) (by fun_prop),
      integral_map (by fun_prop) (by fun_prop)]
    apply integral_congr_ae
    filter_upwards [] with ω
    congr 2
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      one_mul, Fintype.sum_sigma, Y]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum]
    ring
  rw [heq,hiY.charFun_map_fun_sum_eq_prod (fun p => (hY p).aemeasurable)]
  simp only [Finset.prod_apply]
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j _
  have hterm (l : Fin (k j)) : charFun (μ.map (Y ⟨j,l⟩)) 1 =
      charFun (μ.map (X 0)) (t j/r) := by
    dsimp [Y]
    rw [charFun_map_mul_comp (hX _).aemeasurable,mul_one,(hident _).map_eq]
  simp only [hterm,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem gaussian_iid_finite_block_limit {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {x | X 0 x ≠ 0})
    (hsym : IdentDistrib (X 0) (fun x => -X 0 x) μ μ)
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    (k : ℕ → ι → ℕ) (g : (i : ℕ) → (j : ι) → Fin (k i j) → ℕ)
    (hg : ∀ i, Function.Injective (fun p : (j : ι) × Fin (k i j) => g i p.1 p.2))
    (τ : ι → ℝ≥0)
    (hk : ∀ j, Tendsto (fun i => (k i j : ℝ)/fluctuationScale μ (X 0) (r i)) atTop (𝓝 (τ j : ℝ))) :
    TendstoInDistribution
      (fun i ω => WithLp.toLp 2 (fun j => (∑ l, X (g i j l) ω)/r i)) atTop
      (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) (fun _ => μ)
      (Measure.pi (fun j => gaussianReal 0 (τ j))) where
  forall_aemeasurable _ := by fun_prop
  aemeasurable_limit := by fun_prop
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    change Tendsto (fun i => charFun (μ.map (fun ω => WithLp.toLp 2 (fun j => (∑ l, X (g i j l) ω)/r i))) t)
      atTop (𝓝 (charFun ((Measure.pi (fun j => gaussianReal 0 (τ j))).map (WithLp.toLp 2)) t))
    simp only [charFun_independent_finite_blocks μ X hX hind hident _ _ (hg _) _,charFun_pi]
    apply tendsto_finsetProd _
    intro j _
    simpa only [charFun_gaussianReal,Complex.ofReal_zero,mul_zero,zero_mul,zero_sub,
      Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
      Complex.ofReal_ofNat] using
      gaussian_charFun_power_limit_count μ (X 0) (hX 0) hI hne hsym r hr (fun i => k i j) (hk j) (t j)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GridOscillation
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma shifted_iid_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ) (s : ℕ) :
    IdentDistrib (fun ω k => X (s+k) ω) (fun ω k => X k ω) μ μ := by
  exact IdentDistrib.pi (fun k => (hident _).trans (hident k).symm)
    (hind.precomp (fun _ _ h => Nat.add_left_cancel h)) hind

lemma measureReal_shifted_max {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ) (s H : ℕ) (a : ℝ) :
    μ.real {ω | a < partialSumMax (fun k => X (s+k) ω) H} =
      μ.real {ω | a < partialSumMax (fun k => X k ω) H} := by
  apply congrArg ENNReal.toReal
  exact ((shifted_iid_identDistrib μ X hind hident s).comp
    (measurable_partialSumMax (fun k (f : ℕ → ℝ) => f k)
      (fun k => measurable_pi_apply k) H)).measure_mem_eq measurableSet_Ioi

lemma measureReal_max_scaled_fourth_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hne : 0 < μ {ω | X 0 ω ≠ 0}) {r η ε α : ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hε : 0 < ε)
    (_hα : 0 ≤ α) (H s : ℕ) (hH : (H : ℝ) ≤ α*fluctuationScale μ (X 0) r) :
    μ.real {ω | ε*r < partialSumMax (fun k => X (s+k) ω) H} ≤
      α*(fluctuationScale μ (X 0) r*μ.real {ω | η*r < |X 0 ω|}) +
      (32*α*η^2+96*α^2)/ε^4 := by
  rw [measureReal_shifted_max μ X hind hident]
  have hm := truncatedVariance_pos μ (X 0) (hX 0) hne hr
  have hn : 0 < fluctuationScale μ (X 0) r := div_pos (sq_pos_of_pos hr) hm
  have hb := measureReal_iid_max_gt_fourth_bound μ X hX hind hident hsym
    (mul_nonneg hη hr.le) (by nlinarith : η*r ≤ r) (mul_pos hε hr) H
  apply hb.trans
  calc
    _ ≤ (α*fluctuationScale μ (X 0) r)*μ.real {ω | η*r < |X 0 ω|} +
        (32*(α*fluctuationScale μ (X 0) r)*(η*r)^2*truncatedVariance μ (X 0) r+
          96*(α*fluctuationScale μ (X 0) r)^2*(truncatedVariance μ (X 0) r)^2)/(ε*r)^4 := by
      gcongr
    _ = _ := by
      unfold fluctuationScale
      field_simp

lemma gaussian_max_block_eventually {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hne : 0 < μ {ω | X 0 ω ≠ 0}) (r : ℕ → ℝ)
    (hr : IsGaussianSequence μ (X 0) r) {α ε ζ : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε) (hζ : 0 < ζ)
    (H : ℕ → ℕ) (hH : ∀ᶠ i in atTop, (H i : ℝ) ≤ α*fluctuationScale μ (X 0) (r i)) :
    ∀ᶠ i in atTop, ∀ s : ℕ,
      μ.real {ω | ε*r i < partialSumMax (fun k => X (s+k) ω) (H i)} ≤
        128*α^2/ε^4+ζ := by
  have ht := (hr.2 (Real.sqrt α) (Real.sqrt_pos.2 hα)).const_mul α
  have he := (tendsto_order.mp ht).2 ζ (by simpa using hζ)
  filter_upwards [hr.1.eventually (eventually_gt_atTop (0:ℝ)),hH,he] with i hri hHi hti
  intro s
  have hb := measureReal_max_scaled_fourth_le μ X hX hind hident hsym hne hri
    (Real.sqrt_nonneg α) (by simpa using Real.sqrt_le_sqrt hα1) hε hα.le (H i) s hHi
  rw [Real.sq_sqrt hα.le] at hb
  have ha : (32*α*α+96*α^2)/ε^4 = 128*α^2/ε^4 := by ring
  rw [ha] at hb
  linarith

lemma realPartialSum_add (x : ℕ → ℝ) (s n : ℕ) :
    realPartialSum x (s+n) = realPartialSum x s + realPartialSum (fun k => x (s+k)) n := by
  simp only [realPartialSum,Finset.sum_range_add]

lemma grid_oscillation_block {x : ℕ → ℝ} {H j k : ℕ} (hH : 0 < H)
    (hjk : j ≤ k) (hkj : k ≤ j+H) {a : ℝ}
    (hmax : partialSumMax (fun l => x (j/H*H+l)) (2*H) ≤ a) :
    |realPartialSum x k-realPartialSum x j| ≤ 2*a := by
  let s := j/H*H
  have hsj : s ≤ j := Nat.div_mul_le_self j H
  have hsk : s ≤ k := hsj.trans hjk
  have hj2 : j-s ≤ 2*H := by
    have hjrem := Nat.mod_lt j hH
    have hjdecomp : j%H+s = j := by simpa [s,Nat.mul_comm] using Nat.mod_add_div j H
    omega
  have hk2 : k-s ≤ 2*H := by
    have hjrem := Nat.mod_lt j hH
    have hjdecomp : j%H+s = j := by simpa [s,Nat.mul_comm] using Nat.mod_add_div j H
    omega
  have hjb := (abs_partialSum_le_max (fun l => x (s+l)) (j-s)).trans
    ((partialSumMax_mono _ hj2).trans hmax)
  have hkb := (abs_partialSum_le_max (fun l => x (s+l)) (k-s)).trans
    ((partialSumMax_mono _ hk2).trans hmax)
  have hej := realPartialSum_add x s (j-s)
  have hek := realPartialSum_add x s (k-s)
  rw [Nat.add_sub_of_le hsj] at hej
  rw [Nat.add_sub_of_le hsk] at hek
  rw [hej,hek]
  have he : realPartialSum x s + realPartialSum (fun l => x (s+l)) (k-s)-
      (realPartialSum x s + realPartialSum (fun l => x (s+l)) (j-s)) =
      realPartialSum (fun l => x (s+l)) (k-s)-realPartialSum (fun l => x (s+l)) (j-s) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

lemma measureReal_gridOscillation_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    {N H M : ℕ} (hH : 0 < H) (hN : N < M*H) (a : ℝ) :
    μ.real (GridOscillation X N H (2*a)) ≤
      M*μ.real {ω | a < partialSumMax (fun k => X k ω) (2*H)} := by
  let A : ℕ → Set Ω := fun b => {ω | a < partialSumMax (fun k => X (b*H+k) ω) (2*H)}
  have hsub : GridOscillation X N H (2*a) ⊆ ⋃ b ∈ Finset.range M, A b := by
    intro ω hω
    rcases hω with ⟨j,hj,k,_hk,hjk,hkj,hoff⟩
    refine Set.mem_iUnion.mpr ⟨j/H,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr ?_,?_⟩⟩
    · exact (Nat.div_lt_iff_lt_mul hH).2 (hj.trans_lt hN)
    · by_contra h
      exact (not_le_of_gt hoff) (grid_oscillation_block hH hjk hkj (le_of_not_gt h))
  calc
    _ ≤ μ.real (⋃ b ∈ Finset.range M, A b) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ b ∈ Finset.range M, μ.real (A b) := measureReal_biUnion_finset_le _ _
    _ = _ := by
      simp only [A,measureReal_shifted_max μ X hind hident,Finset.sum_const,
        Finset.card_range,nsmul_eq_mul]

lemma eventually_floor_horizon_covered (n : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) (M : ℕ) (hM : T < (M:ℝ)*δ) :
    ∀ᶠ i in atTop, 0 < ⌊δ*n i⌋₊ ∧ ⌊T*n i⌋₊ < M*⌊δ*n i⌋₊ := by
  have hH := (tendsto_nat_floor_mul_div_atTop hδ.le).comp hn
  have hN := (tendsto_nat_floor_mul_div_atTop hT).comp hn
  have hlt := hN.eventually_lt (hH.const_mul (M:ℝ)) hM
  have hpos := (tendsto_order.mp hH).1 (δ/2) (by linarith)
  filter_upwards [hlt,hpos,hn.eventually (eventually_gt_atTop (0:ℝ))] with i hi hp hni
  change (⌊T*n i⌋₊ : ℝ)/n i < (M:ℝ)*((⌊δ*n i⌋₊ : ℝ)/n i) at hi
  change δ/2 < (⌊δ*n i⌋₊ : ℝ)/n i at hp
  have hfloor : 0 < (⌊δ*n i⌋₊ : ℝ) := (div_pos_iff_of_pos_right hni).mp (lt_trans (by linarith) hp)
  refine ⟨by exact_mod_cast hfloor,?_⟩
  rw [← mul_div_assoc] at hi
  have hc := (div_lt_div_iff_of_pos_right hni).mp hi
  exact_mod_cast hc

lemma gaussian_gridOscillation_eventually {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T δ ε ζ : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    (hε : 0 < ε) (hζ : 0 < ζ) (M : ℕ) (hM : T < (M:ℝ)*δ) :
    ∀ᶠ i in atTop,
      μ.real (GridOscillation X ⌊T*fluctuationScale μ (X 0) (r i)⌋₊
        ⌊δ*fluctuationScale μ (X 0) (r i)⌋₊ (ε*r i)) ≤
        M*(8192*δ^2/ε^4+ζ) := by
  let n := fun i => fluctuationScale μ (X 0) (r i)
  have hn : Tendsto n atTop atTop := (fluctuationScale_tendsto μ (X 0) (hX 0) hI hne).comp hr.1
  have hlen : ∀ᶠ i in atTop, ((2*⌊δ*n i⌋₊ : ℕ) : ℝ) ≤ (2*δ)*n i := by
    filter_upwards [hn.eventually (eventually_gt_atTop (0:ℝ))] with i hni
    have hf := Nat.floor_le (mul_nonneg hδ.le hni.le)
    push_cast
    linarith
  have hb := gaussian_max_block_eventually μ X hX hind hident hsym hne r hr
    (by linarith : 0 < 2*δ) (by linarith : 2*δ ≤ 1) (by linarith : 0 < ε/2)
    hζ (fun i => 2*⌊δ*n i⌋₊) hlen
  filter_upwards [hb,eventually_floor_horizon_covered n hn hT hδ M hM] with i hi hcov
  have hm := measureReal_gridOscillation_le μ X hind hident hcov.1 hcov.2 ((ε/2)*r i)
  have he : 2*((ε/2)*r i) = ε*r i := by ring
  rw [he] at hm
  apply hm.trans
  have hb0 := hi 0
  simp only [zero_add] at hb0
  have hec : 128*(2*δ)^2/(ε/2)^4 = 8192*δ^2/ε^4 := by ring
  rw [hec] at hb0
  exact mul_le_mul_of_nonneg_left hb0 (Nat.cast_nonneg M)

theorem gaussian_grid_modulus {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T ε β : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in atTop,
      μ.real (GridOscillation X ⌊T*fluctuationScale μ (X 0) (r i)⌋₊
        ⌊δ*fluctuationScale μ (X 0) (r i)⌋₊ (ε*r i)) ≤ β := by
  have he4 : 0 < ε^4 := pow_pos hε 4
  have hT2 : 0 < T+2 := by linarith
  let δ := min (1/2:ℝ) (β*ε^4/(32768*(T+2)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos (mul_pos hβ he4) (by positivity))
  have hδ1 : δ ≤ 1/2 := min_le_left _ _
  have hbudget : δ*(32768*(T+2)) ≤ β*ε^4 :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  let M := ⌈T/δ⌉₊+1
  have hMpos : 0 < (M:ℝ) := by dsimp [M] <;> positivity
  have hceil := Nat.le_ceil (T/δ)
  have hM : T < (M:ℝ)*δ := by
    have h := (div_le_iff₀ hδ).1 hceil
    dsimp [M]
    push_cast
    nlinarith
  have hMb : (M:ℝ) ≤ T/δ+2 := by
    have hc := Nat.ceil_lt_add_one (div_nonneg hT hδ.le)
    dsimp [M]
    push_cast
    linarith
  have hMδ : (M:ℝ)*δ^2 ≤ (T+2)*δ := by
    have hm : (M:ℝ)*δ ≤ T+2*δ := by
      have hc := mul_le_mul_of_nonneg_right hMb hδ.le
      field_simp at hc
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hm hδ.le]
  have hsmall : (M:ℝ)*(8192*δ^2/ε^4) ≤ β/2 := by
    rw [← mul_div_assoc,div_le_iff₀ he4]
    nlinarith
  have hζ : 0 < β/(2*(M:ℝ)) := div_pos hβ (by positivity)
  refine ⟨δ,hδ,?_⟩
  have hb := gaussian_gridOscillation_eventually μ X hX hind hident hsym hI hne r hr
    hT hδ hδ1 hε hζ M hM
  filter_upwards [hb] with i hi
  apply hi.trans
  rw [mul_add]
  have he : (M:ℝ)*(β/(2*(M:ℝ))) = β/2 := by field_simp
  rw [he]
  linarith

lemma unitRamp_zero {t : ℝ} (ht : t ≤ 0) : unitRamp t = 0 := by
  simp [unitRamp,max_eq_left ht]
lemma unitRamp_one {t : ℝ} (ht : 1 ≤ t) : unitRamp t = 1 := by
  simp [unitRamp,max_eq_right (by linarith : 0 ≤ t),min_eq_left ht]
lemma unitRamp_self {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : unitRamp t = t := by
  simp [unitRamp,max_eq_right ht,min_eq_right ht1]

lemma linearPolygon_formula (x : ℕ → ℝ) (N : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (hN : ⌊t⌋₊ < N) :
    linearPolygon x N t = realPartialSum x ⌊t⌋₊ + (t-⌊t⌋₊)*x ⌊t⌋₊ := by
  let j := ⌊t⌋₊
  have hj : (j:ℝ) ≤ t := Nat.floor_le ht
  have hj1 : t < j+1 := Nat.lt_floor_add_one t
  have hNj : j+1 ≤ N := hN
  have hsplit : N = j+1+(N-(j+1)) := (Nat.add_sub_of_le hNj).symm
  unfold linearPolygon
  rw [hsplit,Finset.sum_range_add,Finset.sum_range_succ]
  have hleft : (∑ k ∈ Finset.range j, unitRamp (t-k)*x k) = realPartialSum x j := by
    unfold realPartialSum
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : (k:ℝ)+1 ≤ j := by exact_mod_cast Finset.mem_range.mp hk
    rw [unitRamp_one (by linarith),one_mul]
  rw [hleft,unitRamp_self (by linarith) (by linarith)]
  have htail : (∑ k ∈ Finset.range (N-(j+1)), unitRamp (t-(j+1+k))*x (j+1+k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    rw [unitRamp_zero (by linarith),zero_mul]
  simpa [j] using congrArg (fun z => realPartialSum x j+(t-j)*x j+z) htail

lemma polygonPath_apply (N : ℕ) (scale : ℝ) (x : ℕ → ℝ) (t : unitInterval) :
    polygonPath N scale x t = linearPolygon x N (scale*t) := by
  simp only [polygonPath,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    ContinuousMap.coe_mk,smul_eq_mul,linearPolygon]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma linearPolygon_near_partialSum {x : ℕ → ℝ} {N : ℕ} {t a : ℝ}
    (ht : 0 ≤ t) (hN : ⌊t⌋₊ < N) (hb : |x ⌊t⌋₊| ≤ a) :
    |linearPolygon x N t-realPartialSum x ⌊t⌋₊| ≤ a := by
  rw [linearPolygon_formula x N ht hN]
  have hj := Nat.floor_le ht
  have hj1 := Nat.lt_floor_add_one t
  have he : realPartialSum x ⌊t⌋₊+(t-⌊t⌋₊)*x ⌊t⌋₊-realPartialSum x ⌊t⌋₊ =
      (t-⌊t⌋₊)*x ⌊t⌋₊ := by ring
  rw [he,abs_mul,abs_of_nonneg (by linarith)]
  have ha : 0 ≤ a := (abs_nonneg _).trans hb
  nlinarith [mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ t-⌊t⌋₊)]

lemma realPartialSum_step (x : ℕ → ℝ) (j : ℕ) :
    realPartialSum x (j+1)-realPartialSum x j = x j := by
  simp [realPartialSum,Finset.sum_range_succ]

lemma not_gridOscillation_bound {Ω : Type*} (X : ℕ → Ω → ℝ) {ω : Ω}
    {N H : ℕ} {a : ℝ} (hω : ω ∉ GridOscillation X N H a)
    {j k : ℕ} (hj : j ≤ N) (hk : k ≤ N) (hd : j ≤ k+H) (hd' : k ≤ j+H) :
    |realPartialSum (fun l => X l ω) k-realPartialSum (fun l => X l ω) j| ≤ a := by
  by_cases hjk : j ≤ k
  · exact le_of_not_gt (fun h => hω ⟨j,hj,k,hk,hjk,hd',h⟩)
  · rw [abs_sub_comm]
    exact le_of_not_gt (fun h => hω ⟨k,hk,j,hj,by omega,hd,h⟩)

lemma linearPolygon_oscillation_le {Ω : Type*} (X : ℕ → Ω → ℝ) {ω : Ω}
    {N H P : ℕ} {a s t : ℝ} (hω : ω ∉ GridOscillation X N H a)
    (hH : 1 ≤ H) (hP : P ≤ N) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hsP : ⌊s⌋₊ < P) (htP : ⌊t⌋₊ < P)
    (hst : ⌊s⌋₊ ≤ ⌊t⌋₊+H) (hts : ⌊t⌋₊ ≤ ⌊s⌋₊+H) :
    |linearPolygon (fun l => X l ω) P t-linearPolygon (fun l => X l ω) P s| ≤ 3*a := by
  have hsb : |X ⌊s⌋₊ ω| ≤ a := by
    rw [← realPartialSum_step (fun l => X l ω)]
    exact not_gridOscillation_bound X hω (by omega) (by omega) (by omega) (by omega)
  have htb : |X ⌊t⌋₊ ω| ≤ a := by
    rw [← realPartialSum_step (fun l => X l ω)]
    exact not_gridOscillation_bound X hω (by omega) (by omega) (by omega) (by omega)
  have hm := not_gridOscillation_bound X hω (j := ⌊s⌋₊) (k := ⌊t⌋₊)
    (by omega) (by omega) hst hts
  have hl := linearPolygon_near_partialSum (x := fun l => X l ω) hs hsP hsb
  have hr := linearPolygon_near_partialSum (x := fun l => X l ω) ht htP htb
  have hb := abs_add_three (linearPolygon (fun l => X l ω) P t-realPartialSum (fun l => X l ω) ⌊t⌋₊)
    (realPartialSum (fun l => X l ω) ⌊t⌋₊-realPartialSum (fun l => X l ω) ⌊s⌋₊)
    (realPartialSum (fun l => X l ω) ⌊s⌋₊-linearPolygon (fun l => X l ω) P s)
  rw [abs_sub_comm (realPartialSum (fun l => X l ω) ⌊s⌋₊)] at hb
  have he : linearPolygon (fun l => X l ω) P t-linearPolygon (fun l => X l ω) P s =
      (linearPolygon (fun l => X l ω) P t-realPartialSum (fun l => X l ω) ⌊t⌋₊)+
      (realPartialSum (fun l => X l ω) ⌊t⌋₊-realPartialSum (fun l => X l ω) ⌊s⌋₊)+
      (realPartialSum (fun l => X l ω) ⌊s⌋₊-linearPolygon (fun l => X l ω) P s) := by ring
  rw [he]
  exact hb.trans (by linarith)

lemma scaledPolygon_apply (x : ℕ → ℝ) (r n T : ℝ) (t : unitInterval) :
    scaledPolygon x r n T t = linearPolygon x (⌊T*n⌋₊+1) (T*n*t)/r := by
  simp [scaledPolygon,polygonPath_apply,div_eq_inv_mul]

lemma scaledPolygon_zero (x : ℕ → ℝ) (r n T : ℝ) :
    scaledPolygon x r n T 0 = 0 := by
  rw [scaledPolygon_apply]
  change (∑ k ∈ Finset.range (⌊T*n⌋₊+1), unitRamp (T*n*(0:ℝ)-k)*x k)/r = 0
  simp only [mul_zero]
  have he : (∑ k ∈ Finset.range (⌊T*n⌋₊+1), unitRamp (0-k)*x k) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [unitRamp_zero (by linarith [Nat.cast_nonneg (α := ℝ) k]),zero_mul]
  rw [he,zero_div]

lemma isOpen_continuousOscillation (ε δ : ℝ) : IsOpen (ContinuousOscillation ε δ) := by
  have he : ContinuousOscillation ε δ =
      ⋃ (s : unitInterval) (t : unitInterval) (_h : dist s t ≤ δ), {f : C(unitInterval,ℝ) | ε < |f s-f t|} := by
    ext f
    simp only [ContinuousOscillation,Set.mem_ofPred_eq,Set.mem_iUnion,exists_prop]
  rw [he]
  exact isOpen_iUnion (fun s => isOpen_iUnion (fun t => isOpen_iUnion (fun _ =>
    isOpen_lt continuous_const ((continuous_eval_const s).sub
      (continuous_eval_const t)).abs)))

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_PathCompact
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma floor_scaled_close {s t u : ℝ} (hs : 0 ≤ s) (_ht : 0 ≤ t)
    (hu : 4 ≤ u) (hst : |s-t| ≤ u/2) : ⌊s⌋₊ ≤ ⌊t⌋₊+⌊u⌋₊ := by
  have h1 := Nat.floor_le hs
  have h2 := Nat.lt_floor_add_one t
  have h3 := Nat.lt_floor_add_one u
  have hb := (abs_le.mp hst).2
  have he : (⌊s⌋₊:ℝ) ≤ (⌊t⌋₊:ℝ)+(⌊u⌋₊:ℝ) := by linarith
  exact_mod_cast he

lemma scaledPolygon_oscillation_subset {Ω : Type*} (X : ℕ → Ω → ℝ)
    {r n T ε δ : ℝ} (hr : 0 < r) (hn : 2 ≤ n) (hT : 0 ≤ T)
    (_hδ : 0 < δ) (hδn : 4 ≤ δ*n) :
    {ω | scaledPolygon (fun k => X k ω) r n T ∈ ContinuousOscillation (3*ε)
      (δ/(2*(T+1)))} ⊆ GridOscillation X ⌊(T+1)*n⌋₊ ⌊δ*n⌋₊ (ε*r) := by
  intro ω hω
  by_contra hg
  rcases hω with ⟨s,t,hst,hbig⟩
  have hn0 : 0 ≤ n := by linarith
  have hTn : 0 ≤ T*n := mul_nonneg hT hn0
  have hs : 0 ≤ T*n*(s:ℝ) := mul_nonneg hTn s.2.1
  have ht : 0 ≤ T*n*(t:ℝ) := mul_nonneg hTn t.2.1
  have hsle : T*n*(s:ℝ) ≤ T*n := mul_le_of_le_one_right hTn s.2.2
  have htle : T*n*(t:ℝ) ≤ T*n := mul_le_of_le_one_right hTn t.2.2
  have hsP : ⌊T*n*(s:ℝ)⌋₊ < ⌊T*n⌋₊+1 := Nat.lt_succ_of_le (Nat.floor_mono hsle)
  have htP : ⌊T*n*(t:ℝ)⌋₊ < ⌊T*n⌋₊+1 := Nat.lt_succ_of_le (Nat.floor_mono htle)
  have hP : ⌊T*n⌋₊+1 ≤ ⌊(T+1)*n⌋₊ := by
    apply Nat.le_floor
    have hf := Nat.floor_le hTn
    push_cast
    nlinarith
  have hH : 1 ≤ ⌊δ*n⌋₊ := by apply Nat.le_floor; norm_num <;> linarith
  have hst' : |(s:ℝ)-(t:ℝ)| ≤ δ/(2*(T+1)) := hst
  have hclose : |T*n*(s:ℝ)-T*n*(t:ℝ)| ≤ (δ*n)/2 := by
    rw [← mul_sub,abs_mul,abs_of_nonneg hTn]
    have h1 := mul_le_mul_of_nonneg_left hst' hTn
    have hden : 0 < 2*(T+1) := by positivity
    have he : T*n*(δ/(2*(T+1))) ≤ δ*n/2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).2
      nlinarith [mul_nonneg _hδ.le hn0]
    exact h1.trans he
  have hb := linearPolygon_oscillation_le X hg hH hP hs ht hsP htP
    (floor_scaled_close hs ht hδn hclose)
    (floor_scaled_close ht hs hδn (by simpa [abs_sub_comm] using hclose))
  simp only [scaledPolygon_apply] at hbig
  rw [← sub_div,abs_div,abs_of_pos hr] at hbig
  have hlarge := (lt_div_iff₀ hr).mp hbig
  rw [abs_sub_comm] at hb
  nlinarith

theorem gaussian_continuous_modulus {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T ε β : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in atTop,
      μ.real {ω | scaledPolygon (fun k => X k ω) (r i)
        (fluctuationScale μ (X 0) (r i)) T ∈ ContinuousOscillation ε δ} ≤ β := by
  let n := fun i => fluctuationScale μ (X 0) (r i)
  have hn : Tendsto n atTop atTop := (fluctuationScale_tendsto μ (X 0) (hX 0) hI hne).comp hr.1
  obtain ⟨δ,hδ,hb⟩ := gaussian_grid_modulus μ X hX hind hident hsym hI hne r hr
    (T := T+1) (ε := ε/3) (by linarith) (by positivity) hβ
  refine ⟨δ/(2*(T+1)),by positivity,?_⟩
  have hδn : Tendsto (fun i => δ*n i) atTop atTop := hn.const_mul_atTop hδ
  filter_upwards [hb,hr.1.eventually (eventually_gt_atTop (0:ℝ)),
    hn.eventually (eventually_ge_atTop (2:ℝ)),hδn.eventually (eventually_ge_atTop (4:ℝ))]
    with i hi hri hni hdni
  have hs := scaledPolygon_oscillation_subset X hri hni hT hδ hdni (ε := ε/3)
  have he : 3*(ε/3)=ε := by ring
  rw [he] at hs
  exact (measureReal_mono hs (measure_ne_top _ _)).trans hi

lemma linearPolygon_abs_le_max (x : ℕ → ℝ) {N : ℕ} {t : ℝ}
    (ht : 0 ≤ t) (hN : ⌊t⌋₊ < N) : |linearPolygon x N t| ≤ partialSumMax x N := by
  let j := ⌊t⌋₊
  have hj : (j:ℝ) ≤ t := Nat.floor_le ht
  have hj1 : t < j+1 := Nat.lt_floor_add_one t
  have h1 := (abs_partialSum_le_max x j).trans (partialSumMax_mono x hN.le)
  have h2 := (abs_partialSum_le_max x (j+1)).trans (partialSumMax_mono x hN)
  rw [linearPolygon_formula x N ht hN]
  have he : realPartialSum x j+(t-j)*x j =
      (1-(t-j))*realPartialSum x j+(t-j)*realPartialSum x (j+1) := by
    rw [realPartialSum_succ]
    ring
  change |realPartialSum x j+(t-j)*x j| ≤ _
  rw [he]
  calc
    _ ≤ |(1-(t-j))*realPartialSum x j|+|(t-j)*realPartialSum x (j+1)| := abs_add_le _ _
    _ = (1-(t-j))*|realPartialSum x j|+(t-j)*|realPartialSum x (j+1)| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (show 0 ≤ 1-(t-j) by linarith),
        abs_of_nonneg (show 0 ≤ t-j by linarith)]
    _ ≤ (1-(t-j))*partialSumMax x N+(t-j)*partialSumMax x N := by gcongr; linarith
    _ = _ := by ring

lemma norm_scaledPolygon_le_max (x : ℕ → ℝ) {r n T : ℝ}
    (hr : 0 < r) (hn : 0 ≤ n) (hT : 0 ≤ T) :
    ‖scaledPolygon x r n T‖ ≤ partialSumMax x (⌊T*n⌋₊+1)/r := by
  apply (ContinuousMap.norm_le_of_nonempty _).mpr
  intro t
  rw [Real.norm_eq_abs,scaledPolygon_apply,abs_div,abs_of_pos hr]
  apply (div_le_div_iff_of_pos_right hr).2
  apply linearPolygon_abs_le_max
  · exact mul_nonneg (mul_nonneg hT hn) t.2.1
  · exact Nat.lt_succ_of_le (Nat.floor_mono (mul_le_of_le_one_right (mul_nonneg hT hn) t.2.2))

lemma gaussian_max_horizon_eventually {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hne : 0 < μ {ω | X 0 ω ≠ 0}) (r : ℕ → ℝ)
    (hr : IsGaussianSequence μ (X 0) r) {α ε β : ℝ}
    (hα : 0 ≤ α) (hε : 0 < ε) (hβ : 0 < β)
    (H : ℕ → ℕ) (hH : ∀ᶠ i in atTop, (H i : ℝ) ≤ α*fluctuationScale μ (X 0) (r i)) :
    ∀ᶠ i in atTop, μ.real {ω | ε*r i < partialSumMax (fun k => X k ω) (H i)} ≤
      (32*α+96*α^2)/ε^4+β := by
  have he := (hr.2 1 zero_lt_one).const_mul α
  have hb := (tendsto_order.mp he).2 β (by simpa using hβ)
  filter_upwards [hb,hH,hr.1.eventually (eventually_gt_atTop (0:ℝ))] with i hi hHi hri
  have h := measureReal_max_scaled_fourth_le μ X hX hind hident hsym hne hri
    (η := 1) zero_le_one le_rfl hε hα (H i) 0 hHi
  simp only [Nat.zero_add,one_mul,one_pow,mul_one] at h hi
  linarith

lemma gaussian_continuous_norm_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T β : ℝ} (hT : 0 ≤ T) (hβ : 0 < β) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ i in atTop,
      μ.real {ω | R < ‖scaledPolygon (fun k => X k ω) (r i)
        (fluctuationScale μ (X 0) (r i)) T‖} ≤ β := by
  let n := fun i => fluctuationScale μ (X 0) (r i)
  let C := 32*(T+1)+96*(T+1)^2
  have hC : 0 < C := by dsimp [C] <;> positivity
  let R := max 1 (2*C/β)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hRβ : 2*C ≤ R*β := (div_le_iff₀ hβ).mp (le_max_right _ _)
  have hR4 : R ≤ R^4 := by nlinarith [sq_nonneg (R-1),sq_nonneg (R^2-1)]
  have hsmall : C/R^4 ≤ β/2 := by
    rw [div_le_iff₀ (pow_pos hR 4)]
    nlinarith
  have hn : Tendsto n atTop atTop := (fluctuationScale_tendsto μ (X 0) (hX 0) hI hne).comp hr.1
  have hH : ∀ᶠ i in atTop, (⌊T*n i⌋₊+1 : ℝ) ≤ (T+1)*n i := by
    filter_upwards [hn.eventually (eventually_ge_atTop (1:ℝ))] with i hi
    have hf := Nat.floor_le (mul_nonneg hT (by linarith : 0 ≤ n i))
    nlinarith
  have hH' : ∀ᶠ i in atTop, ((⌊T*n i⌋₊+1:ℕ):ℝ) ≤ (T+1)*n i := by simpa using hH
  have hb := gaussian_max_horizon_eventually μ X hX hind hident hsym hne r hr
    (by linarith : 0 ≤ T+1) hR (by linarith : 0 < β/2) (fun i => ⌊T*n i⌋₊+1) hH'
  refine ⟨R,hR,?_⟩
  filter_upwards [hb,hn.eventually (eventually_ge_atTop (0:ℝ)),
    hr.1.eventually (eventually_gt_atTop (0:ℝ))] with i hi hni hri
  have hs : {ω | R < ‖scaledPolygon (fun k => X k ω) (r i) (n i) T‖} ⊆
      {ω | R*r i < partialSumMax (fun k => X k ω) (⌊T*n i⌋₊+1)} := by
    intro ω hω
    exact (lt_div_iff₀ hri).mp (hω.trans_le (norm_scaledPolygon_le_max _ hri hni hT))
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans hi).trans (by linarith)

lemma continuousOscillation_mono {ε δ δ' : ℝ} (hδ : δ ≤ δ') :
    ContinuousOscillation ε δ ⊆ ContinuousOscillation ε δ' := by
  rintro f ⟨s,t,hst,h⟩
  exact ⟨s,t,hst.trans hδ,h⟩

lemma continuousOscillation_iInter_empty {ε : ℝ} (hε : 0 < ε) :
    (⋂ m : ℕ, ContinuousOscillation ε (1/(m+1))) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro f hf
  obtain ⟨δ,hδ,hfδ⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous) ε hε
  have hm := (tendsto_order.mp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 δ hδ
  obtain ⟨m,hm⟩ := hm.exists
  rcases Set.mem_iInter.mp hf m with ⟨s,t,hst,hbig⟩
  have hc := hfδ (hst.trans_lt hm)
  exact (not_lt_of_ge hbig.le) (by simpa [Real.dist_eq] using hc)

lemma tendsto_measure_continuousOscillation (μ : Measure C(unitInterval,ℝ))
    [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m : ℕ => μ (ContinuousOscillation ε (1/(m+1)))) atTop (𝓝 0) := by
  have ha : Antitone (fun m : ℕ => ContinuousOscillation ε (1/(m+1))) := by
    intro j k hjk
    apply continuousOscillation_mono
    gcongr
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (fun m : ℕ => (isOpen_continuousOscillation ε (1/(m+1))).measurableSet.nullMeasurableSet)
    ha ⟨0,measure_ne_top _ _⟩
  rw [continuousOscillation_iInter_empty hε,measure_empty] at h
  exact h

lemma continuous_modulus_uniform_of_eventual
    (μ : ℕ → Measure C(unitInterval,ℝ)) [∀ i, IsFiniteMeasure (μ i)]
    (h : ∀ ε β : ℝ, 0 < ε → 0 < β → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ i in atTop, μ i (ContinuousOscillation ε δ) ≤ ENNReal.ofReal β) :
    ∀ ε β : ℝ, 0 < ε → 0 < β → ∃ δ : ℝ, 0 < δ ∧
      ∀ i, μ i (ContinuousOscillation ε δ) ≤ ENNReal.ofReal β := by
  intro ε β hε hβ
  obtain ⟨δ,hδ,hb⟩ := h ε β hε hβ
  obtain ⟨N,hN⟩ := eventually_atTop.1 hb
  have he : ∀ᶠ m : ℕ in atTop, ∀ j : Fin N,
      μ j (ContinuousOscillation ε (1/(m+1))) ≤ ENNReal.ofReal β := by
    apply eventually_all.2
    intro j
    exact ((tendsto_order.mp (tendsto_measure_continuousOscillation (μ j) hε)).2
      _ (ENNReal.ofReal_pos.mpr hβ)).mono (fun _ hm => hm.le)
  obtain ⟨m,hm⟩ := he.exists
  refine ⟨min δ (1/(m+1)),lt_min hδ (by positivity),?_⟩
  intro i
  by_cases hi : N ≤ i
  · exact (measure_mono (continuousOscillation_mono (min_le_left _ _))).trans (hN i hi)
  · exact (measure_mono (continuousOscillation_mono (min_le_right _ _))).trans
      (hm ⟨i,by omega⟩)

lemma continuous_norm_uniform_of_eventual
    (μ : ℕ → Measure C(unitInterval,ℝ)) [∀ i, IsFiniteMeasure (μ i)]
    (h : ∀ β : ℝ, 0 < β → ∃ R : ℝ, 0 < R ∧
      ∀ᶠ i in atTop, μ i {f | R < ‖f‖} ≤ ENNReal.ofReal β) :
    ∀ β : ℝ, 0 < β → ∃ R : ℝ, 0 < R ∧
      ∀ i, μ i {f | R < ‖f‖} ≤ ENNReal.ofReal β := by
  intro β hβ
  obtain ⟨R,hR,hb⟩ := h β hβ
  obtain ⟨N,hN⟩ := eventually_atTop.1 hb
  have he : ∀ᶠ r : ℝ in atTop, ∀ j : Fin N,
      μ j {f | r < ‖f‖} ≤ ENNReal.ofReal β := by
    apply eventually_all.2
    intro j
    have ht := tendsto_measure_norm_gt_of_isTightMeasureSet
      (isTightMeasureSet_singleton (μ := μ j))
    simp only [Set.mem_singleton_iff,iSup_iSup_eq_left] at ht
    exact ((tendsto_order.mp ht).2 _ (ENNReal.ofReal_pos.mpr hβ)).mono (fun _ hm => hm.le)
  obtain ⟨r,hr⟩ := he.exists
  refine ⟨max R r, hR.trans_le (le_max_left _ _),?_⟩
  intro i
  by_cases hi : N ≤ i
  · exact (measure_mono (μ := μ i) (show {f : C(unitInterval,ℝ) | max R r < ‖f‖} ⊆ {f | R < ‖f‖} from fun _ hf => (le_max_left R r).trans_lt hf)).trans (hN i hi)
  · exact (measure_mono (μ := μ i) (show {f : C(unitInterval,ℝ) | max R r < ‖f‖} ⊆ {f | r < ‖f‖} from fun _ hf => (le_max_right R r).trans_lt hf)).trans
      (hr ⟨i,by omega⟩)

lemma isClosed_pathCompact (R : ℝ) (δ : ℕ → ℝ) : IsClosed (pathCompact R δ) := by
  exact (isClosed_le continuous_norm continuous_const).inter
    (isClosed_iInter (fun m => (isOpen_continuousOscillation _ _).isClosed_compl))

lemma isCompact_pathCompact (R : ℝ) (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) :
    IsCompact (pathCompact R δ) := by
  let e := ContinuousMap.isometryEquivBoundedOfCompact unitInterval ℝ
  have hc : IsCompact (e.symm ⁻¹' pathCompact R δ) := by
    apply BoundedContinuousFunction.arzela_ascoli₂ (Set.Icc (-R) R) isCompact_Icc
      (e.symm ⁻¹' pathCompact R δ) ((isClosed_pathCompact R δ).preimage e.symm.continuous)
    · intro f t hf
      have hnorm : ‖e.symm f‖ ≤ R := hf.1
      have hval := ContinuousMap.norm_coe_le_norm (e.symm f) t
      have habs : |f t| ≤ R := hval.trans hnorm
      exact abs_le.mp habs
    · intro t
      apply Metric.equicontinuousAt_iff.2
      intro ε hε
      have hm := (tendsto_order.mp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 ε hε
      obtain ⟨m,hm⟩ := hm.exists
      refine ⟨δ m,hδ m,?_⟩
      intro s hst f
      have hf := Set.mem_iInter.mp f.2.2 m
      have hb : |f.1 t-f.1 s| ≤ 1/(m+1) := by
        by_contra! hb
        exact hf ⟨t,s,by simpa [dist_comm] using hst.le,hb⟩
      simpa [Real.dist_eq] using hb.trans_lt hm
  have he : e.symm '' (e.symm ⁻¹' pathCompact R δ) = pathCompact R δ :=
    Set.image_preimage_eq _ e.symm.surjective
  rw [← he]
  exact hc.image e.symm.continuous

lemma isTightMeasureSet_of_continuous_modulus
    (μ : ℕ → Measure C(unitInterval,ℝ)) [∀ i, IsFiniteMeasure (μ i)]
    (hnorm : ∀ β : ℝ, 0 < β → ∃ R : ℝ, 0 < R ∧
      ∀ᶠ i in atTop, μ i {f | R < ‖f‖} ≤ ENNReal.ofReal β)
    (hmod : ∀ ε β : ℝ, 0 < ε → 0 < β → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ i in atTop, μ i (ContinuousOscillation ε δ) ≤ ENNReal.ofReal β) :
    IsTightMeasureSet (Set.range μ) := by
  have hn := continuous_norm_uniform_of_eventual μ hnorm
  have hm := continuous_modulus_uniform_of_eventual μ hmod
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.2
  intro ε hε
  obtain ⟨b,hb,hbs⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  obtain ⟨R,hR,hRb⟩ := hn (b 0) (by exact_mod_cast hb 0)
  have hd : ∀ m : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ i,
      μ i (ContinuousOscillation (1/(m+1)) δ) ≤ (b (m+1) : ℝ≥0∞) := by
    intro m
    simpa only [ENNReal.ofReal_coe_nnreal] using
      hm (1/(m+1)) (b (m+1)) (by positivity) (by exact_mod_cast hb (m+1))
  choose δ hδ hd using hd
  refine ⟨pathCompact R δ,isCompact_pathCompact R δ hδ,?_⟩
  rintro _ ⟨i,rfl⟩
  have he : (pathCompact R δ)ᶜ = {f | R < ‖f‖} ∪
      ⋃ m : ℕ, ContinuousOscillation (1/(m+1)) (δ m) := by
    ext f
    simp [pathCompact,imp_iff_not_or]
  rw [he]
  calc
    _ ≤ μ i {f | R < ‖f‖}+μ i (⋃ m : ℕ, ContinuousOscillation (1/(m+1)) (δ m)) := measure_union_le _ _
    _ ≤ (b 0 : ℝ≥0∞) + ∑' m : ℕ, (b (m+1) : ℝ≥0∞) := by
      gcongr
      · simpa only [ENNReal.ofReal_coe_nnreal] using hRb i
      · exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum (fun m => hd m i))
    _ = ∑' m : ℕ, (b m : ℝ≥0∞) := (tsum_eq_zero_add' (f := fun m : ℕ => (b m : ℝ≥0∞)) ENNReal.summable).symm
    _ ≤ ε := hbs.le

theorem gaussian_iid_path_tight {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T : ℝ} (hT : 0 ≤ T) :
    IsTightMeasureSet (Set.range (fun i => μ.map (fun ω =>
      scaledPolygon (fun k => X k ω) (r i) (fluctuationScale μ (X 0) (r i)) T))) := by
  let P := fun i ω => scaledPolygon (fun k => X k ω) (r i)
    (fluctuationScale μ (X 0) (r i)) T
  have hP : ∀ i, Measurable (P i) := fun i => measurable_scaledPolygon X hX _ _ _
  have : ∀ i, IsProbabilityMeasure (μ.map (P i)) := fun i =>
    (Measure.isProbabilityMeasure_map_iff (hP i).aemeasurable).mpr inferInstance
  apply isTightMeasureSet_of_continuous_modulus
  · intro β hβ
    obtain ⟨R,hR,hb⟩ := gaussian_continuous_norm_bound μ X hX hind hident hsym hI hne r hr hT hβ
    refine ⟨R,hR,hb.mono (fun i hi => ?_)⟩
    rw [Measure.map_apply (hP i) (isOpen_lt continuous_const continuous_norm).measurableSet]
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hβ.le).2 hi
  · intro ε β hε hβ
    obtain ⟨δ,hδ,hb⟩ := gaussian_continuous_modulus μ X hX hind hident hsym hI hne r hr hT hε hβ
    refine ⟨δ,hδ,hb.mono (fun i hi => ?_)⟩
    rw [Measure.map_apply (hP i) (isOpen_continuousOscillation ε δ).measurableSet]
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hβ.le).2 hi

lemma tendstoInMeasure_pi {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : ℕ → Ω → ι → ℝ)
    (h : ∀ j, TendstoInMeasure μ (fun n ω => F n ω j) atTop 0) :
    TendstoInMeasure μ F atTop 0 := by
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  have ht : Tendsto (fun n => ∑ j, μ.real {ω | ε ≤ |F n ω j|}) atTop (𝓝 0) := by
    convert tendsto_finsetSum Finset.univ (fun j _ =>
      (tendstoInMeasure_iff_measureReal_norm.1 (h j)) ε hε) using 1 <;>
      simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs,Finset.sum_const_zero]
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro n
  have hs : {ω | ε ≤ ‖F n ω-(0 : Ω → ι → ℝ) ω‖} ⊆ ⋃ j, {ω | ε ≤ |F n ω j|} := by
    intro ω hω
    by_contra! hc
    have hl : ‖F n ω‖ < ε := (pi_norm_lt_iff hε).2 (by simpa [Real.norm_eq_abs] using hc)
    exact (not_lt_of_ge (show ε ≤ ‖F n ω‖ by simpa using hω)) hl
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (measureReal_iUnion_fintype_le _)

lemma tendstoInMeasure_of_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F G : ℕ → Ω → ℝ)
    (hG : TendstoInMeasure μ G atTop 0)
    (hb : ∀ᶠ n in atTop, ∀ ω, |F n ω| ≤ |G n ω|) :
    TendstoInMeasure μ F atTop 0 := by
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  have hg := (tendstoInMeasure_iff_measureReal_norm.1 hG) ε hε
  simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs] at hg ⊢
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hg
  filter_upwards [hb] with n hn
  exact measureReal_mono (fun ω hω => hω.trans (hn ω)) (measure_ne_top _ _)

lemma selected_iid_div_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : Measurable (X 0)) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) (k : ℕ → ℕ) :
    TendstoInMeasure μ (fun n ω => X (k n) ω/r n) atTop 0 := by
  have h0 : TendstoInMeasure μ (fun n ω => X 0 ω/r n) atTop 0 := by
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hX.div_const _).aestronglyMeasurable)
    filter_upwards [] with ω
    exact tendsto_const_nhds.div_atTop hr
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  have he n : μ.real {ω | ε ≤ ‖X (k n) ω/r n-(0 : Ω → ℝ) ω‖} =
      μ.real {ω | ε ≤ ‖X 0 ω/r n-(0 : Ω → ℝ) ω‖} := by
    simp only [Pi.zero_apply,sub_zero]
    unfold Measure.real
    apply congrArg ENNReal.toReal
    exact ((hident (k n)).comp (show Measurable (fun x : ℝ => x/r n) by fun_prop)).measure_mem_eq
      (s := {x : ℝ | ε ≤ ‖x‖}) (isClosed_le continuous_const continuous_norm).measurableSet
  simp_rw [he]
  exact (tendstoInMeasure_iff_measureReal_norm.1 h0) ε hε

lemma polygon_eval_error_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : Measurable (X 0)) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (r n : ℕ → ℝ) (hr : Tendsto r atTop atTop) (hn : ∀ᶠ i in atTop, 0 ≤ n i)
    {T : ℝ} (hT : 0 ≤ T) (s : unitInterval) :
    TendstoInMeasure μ (fun i ω => scaledPolygon (fun k => X k ω) (r i) (n i) T s -
      realPartialSum (fun k => X k ω) ⌊(T*s)*n i⌋₊/r i) atTop 0 := by
  have hsel := selected_iid_div_tendstoInMeasure μ X hX hident r hr (fun i => ⌊(T*s)*n i⌋₊)
  apply tendstoInMeasure_of_abs_le μ _ _ hsel
  filter_upwards [hn,hr.eventually (eventually_gt_atTop (0:ℝ))] with i hni hri
  intro ω
  rw [scaledPolygon_apply]
  have he : T*n i*s = (T*s)*n i := by ring
  rw [he,← sub_div,abs_div,abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  apply linearPolygon_near_partialSum
  · exact mul_nonneg (mul_nonneg hT s.2.1) hni
  · apply Nat.lt_succ_of_le
    apply Nat.floor_mono
    calc
      (T*s)*n i = (T*n i)*s := by ring
      _ ≤ T*n i := mul_le_of_le_one_right (mul_nonneg hT hni) s.2.2
  · exact le_rfl

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OrderedTimes
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma gaussian_block_count_limit {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun i => ((⌊b*n i⌋₊-⌊a*n i⌋₊:ℕ):ℝ)/n i) atTop (𝓝 (b-a)) := by
  have he : (fun i => ((⌊b*n i⌋₊-⌊a*n i⌋₊:ℕ):ℝ)/n i) =ᶠ[atTop]
      fun i => (⌊b*n i⌋₊:ℝ)/n i-(⌊a*n i⌋₊:ℝ)/n i := by
    filter_upwards [hn.eventually (eventually_ge_atTop (0:ℝ))] with i hi
    rw [Nat.cast_sub (Nat.floor_mono (mul_le_mul_of_nonneg_right hab hi)),sub_div]
  apply Tendsto.congr' he.symm
  exact ((tendsto_nat_floor_mul_div_atTop (ha.trans hab)).comp hn).sub
    ((tendsto_nat_floor_mul_div_atTop ha).comp hn)

lemma tendstoInMeasure_sub_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F G : ℕ → Ω → ℝ)
    (hF : TendstoInMeasure μ F atTop 0) (hG : TendstoInMeasure μ G atTop 0) :
    TendstoInMeasure μ (F-G) atTop 0 := by
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  have hf := (tendstoInMeasure_iff_measureReal_norm.1 hF) (ε/2) (by positivity)
  have hg := (tendstoInMeasure_iff_measureReal_norm.1 hG) (ε/2) (by positivity)
  simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs] at hf hg ⊢
  have hs n : {ω | ε ≤ |(F-G) n ω|} ⊆
      {ω | ε/2 ≤ |F n ω|} ∪ {ω | ε/2 ≤ |G n ω|} := by
    intro ω hω
    by_contra! hc
    simp only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_le] at hc
    have ht := abs_sub (F n ω) (G n ω)
    change ε ≤ |F n ω-G n ω| at hω
    exact (not_lt_of_ge hω) (ht.trans_lt (by linarith))
  have hb n := (measureReal_mono (μ := μ) (hs n) (measure_ne_top _ _)).trans (measureReal_union_le (μ := μ) _ _)
  exact squeeze_zero (fun _ => measureReal_nonneg) hb (by simpa using hf.add hg)

lemma fluctuationScale_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (r : ℝ) : 0 ≤ fluctuationScale μ S r := by
  apply div_nonneg (sq_nonneg _)
  exact integral_nonneg (fun x => le_min (sq_nonneg _) (sq_nonneg _))

lemma disjoint_blocks_injective {ι : Type*} (a b : ι → ℕ)
    (hdisj : ∀ j k, j ≠ k → b j ≤ a k ∨ b k ≤ a j) :
    Function.Injective (fun p : (j : ι) × Fin (b j-a j) => a p.1+p.2.1) := by
  rintro ⟨j,l⟩ ⟨k,m⟩ he
  have hj : l.1 < b j-a j := l.2
  have hk : m.1 < b k-a k := m.2
  by_cases hjk : j = k
  · subst k
    have hlm : l = m := Fin.ext (by simpa using he)
    subst m
    rfl
  · rcases hdisj j k hjk with h|h <;> simp only at he <;> omega

lemma realPartialSum_sub_eq_block (x : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    realPartialSum x b-realPartialSum x a = ∑ l : Fin (b-a), x (a+l) := by
  have h := realPartialSum_add x a (b-a)
  rw [Nat.add_sub_of_le hab] at h
  rw [Fin.sum_univ_eq_sum_range (f := fun l => x (a+l))]
  change _ = realPartialSum (fun l => x (a+l)) (b-a)
  linarith

theorem gaussian_polygon_increment_limit {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {x | X 0 x ≠ 0})
    (hsym : IdentDistrib (X 0) (fun x => -X 0 x) μ μ)
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T : ℝ} (hT : 0 ≤ T) (a b : ι → unitInterval)
    (hab : ∀ j, a j ≤ b j)
    (hdisj : ∀ j k, j ≠ k → b j ≤ a k ∨ b k ≤ a j) :
    TendstoInDistribution (fun i ω (j : ι) =>
      scaledPolygon (fun k => X k ω) (r i) (fluctuationScale μ (X 0) (r i)) T (b j)-
      scaledPolygon (fun k => X k ω) (r i) (fluctuationScale μ (X 0) (r i)) T (a j))
      atTop id (fun _ => μ) (Measure.pi (fun j : ι => gaussianReal 0
        (Real.toNNReal (T*((b j : ℝ)-a j))))) := by
  let n := fun i => fluctuationScale μ (X 0) (r i)
  have hn := (fluctuationScale_tendsto μ (X 0) (hX 0) hI hne).comp hr.1
  have hn0 i : 0 ≤ n i := fluctuationScale_nonneg _ _ _
  let A := fun i j => ⌊(T*a j)*n i⌋₊
  let B := fun i j => ⌊(T*b j)*n i⌋₊
  have hAB i j : A i j ≤ B i j := Nat.floor_mono
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hab j) hT) (hn0 i))
  have hd i j k (hjk : j ≠ k) : B i j ≤ A i k ∨ B i k ≤ A i j := by
    rcases hdisj j k hjk with h|h
    · exact Or.inl (Nat.floor_mono (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hT) (hn0 i)))
    · exact Or.inr (Nat.floor_mono (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hT) (hn0 i)))
  let τ : ι → ℝ≥0 := fun j => Real.toNNReal (T*((b j : ℝ)-a j))
  have hc j : Tendsto (fun i => ((B i j-A i j:ℕ):ℝ)/n i) atTop (𝓝 (τ j : ℝ)) := by
    have h := gaussian_block_count_limit (mul_nonneg hT (a j).2.1)
      (mul_le_mul_of_nonneg_left (hab j) hT) n hn
    dsimp only [τ]
    rw [Real.coe_toNNReal _ (mul_nonneg hT (sub_nonneg.mpr (hab j)))]
    simpa only [A,B,mul_sub] using h
  have hb := gaussian_iid_finite_block_limit μ X hX hind hident hI hne hsym r hr
    (fun i j => B i j-A i j) (fun i j l => A i j+l)
    (fun i => disjoint_blocks_injective (A i) (B i) (hd i)) τ hc
  have hb' := hb.continuous_comp (g := (WithLp.ofLp : EuclideanSpace ℝ ι → (ι → ℝ))) (by fun_prop)
  let Z := fun i ω j => (∑ l : Fin (B i j-A i j), X (A i j+l) ω)/r i
  have hZ : TendstoInDistribution Z atTop id (fun _ => μ)
      (Measure.pi (fun j => gaussianReal 0 (τ j))) := by
    convert hb' using 1 <;> rfl
  let Y := fun i ω j => scaledPolygon (fun k => X k ω) (r i) (n i) T (b j)-
    scaledPolygon (fun k => X k ω) (r i) (n i) T (a j)
  apply tendstoInDistribution_of_tendstoInMeasure_sub Y id hZ
  · apply tendstoInMeasure_pi
    intro j
    have ha := polygon_eval_error_tendstoInMeasure μ X (hX 0) hident r n hr.1
      (Eventually.of_forall hn0) hT (a j)
    have hb := polygon_eval_error_tendstoInMeasure μ X (hX 0) hident r n hr.1
      (Eventually.of_forall hn0) hT (b j)
    have he := tendstoInMeasure_sub_zero μ _ _ hb ha
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    ext i ω
    change Y i ω j-Z i ω j = _
    dsimp [Y,Z]
    rw [← realPartialSum_sub_eq_block (fun k => X k ω) (hAB i j)]
    dsimp [A,B]
    ring
  · intro i
    apply Measurable.aemeasurable
    apply Measurable.of_eval
    intro j
    exact ((continuous_eval_const _).measurable.comp (measurable_scaledPolygon X hX _ _ _)).sub
      ((continuous_eval_const _).measurable.comp (measurable_scaledPolygon X hX _ _ _))

lemma orderedTimes_monotone (I : Finset unitInterval) : Monotone (orderedTimes I) := by
  intro i j hij
  obtain rfl | hi := eq_or_ne i 0
  · simp [orderedTimes]
  have hj : j ≠ 0 := by intro hj; subst j; exact hi (le_antisymm hij (Fin.zero_le _))
  rw [orderedTimes,dite_eq_right hi,orderedTimes,dite_eq_right hj]
  exact OrderEmbedding.monotone _ (by simpa)

lemma incrementCumsum_eval (I : Finset unitInterval) (f : unitInterval → ℝ) (hf : f 0 = 0) :
    I.restrict f = incrementCumsum I (fun j => f (orderedTimes I j.succ)-f (orderedTimes I j.castSucc)) := by
  ext t
  simp only [Finset.restrict,incrementCumsum,ContinuousLinearMap.coe_mk',LinearMap.coe_mk,AddHom.coe_mk]
  rw [Fin.sum_Iic_sub _ (fun j => f (orderedTimes I j))]
  simp [orderedTimes,hf,Finset.orderEmbOfFin]

lemma ordered_adjacent_disjoint {m : ℕ} (t : Fin (m+1) → unitInterval) (ht : Monotone t) :
    ∀ j k : Fin m, j ≠ k → t j.succ ≤ t k.castSucc ∨ t k.succ ≤ t j.castSucc := by
  intro j k hjk
  rcases lt_or_gt_of_ne hjk with h|h
  · exact Or.inl (ht (by exact_mod_cast h))
  · exact Or.inr (ht (by exact_mod_cast h))

theorem gaussian_polygon_finite_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {x | X 0 x ≠ 0})
    (hsym : IdentDistrib (X 0) (fun x => -X 0 x) μ μ)
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T : ℝ} (hT : 0 ≤ T) (I : Finset unitInterval) :
    TendstoInDistribution (fun i ω => I.restrict
      (scaledPolygon (fun k => X k ω) (r i) (fluctuationScale μ (X 0) (r i)) T))
      atTop id (fun _ => μ) (gaussianPathFiniteLaw T I) := by
  let Y := fun i ω => scaledPolygon (fun k => X k ω) (r i)
    (fluctuationScale μ (X 0) (r i)) T
  let t := orderedTimes I
  have ht : Monotone t := orderedTimes_monotone I
  have hi := gaussian_polygon_increment_limit μ X hX hind hident hI hne hsym r hr hT
    (fun j : Fin I.card => t j.castSucc) (fun j => t j.succ)
    (fun j => ht (Fin.castSucc_le_succ j)) (ordered_adjacent_disjoint t ht)
  have hc := hi.continuous_comp (incrementCumsum I).continuous
  have hl i : (fun ω => I.restrict ((Y i ω) ·)) =ᵐ[μ]
      (incrementCumsum I) ∘ (fun ω j => Y i ω (t j.succ)-Y i ω (t j.castSucc)) := by
    filter_upwards [] with ω
    exact incrementCumsum_eval I (Y i ω) (scaledPolygon_zero _ _ _ _)
  have hc' := hc.congr (fun i => (hl i).symm) Filter.EventuallyEq.rfl
  refine ⟨hc'.forall_aemeasurable,measurable_id.aemeasurable,?_⟩
  convert hc'.tendsto using 1
  all_goals try with_reducible_and_instances rfl
  simp only [gaussianPathFiniteLaw,Function.comp_def,id_eq,Measure.map_id]
  rfl

lemma continuous_path_measure_ext (μ ν : Measure C(unitInterval,ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ I : Finset unitInterval, μ.map (fun f : C(unitInterval,ℝ) => I.restrict f) =
      ν.map (fun f : C(unitInterval,ℝ) => I.restrict f)) : μ = ν := by
  classical
  let e := TopologicalSpace.denseSeq unitInterval
  let E := fun f : C(unitInterval,ℝ) => fun n => f (e n)
  have hE : Continuous E := continuous_pi (fun n => continuous_eval_const _)
  have hEinj : Function.Injective E := by
    intro f g hfg
    apply ContinuousMap.coe_injective
    exact TopologicalSpace.denseRange_denseSeq unitInterval |>.equalizer
      f.continuous g.continuous hfg
  apply hE.measurableEmbedding hEinj |>.map_injective
  let P := fun J : Finset ℕ => (μ.map E).map J.restrict
  have : ∀ J, IsFiniteMeasure (P J) := fun _ => inferInstance
  apply IsProjectiveLimit.unique (P := P) (fun _ => rfl)
  intro J
  let I := J.image e
  let g := fun f : I → ℝ => fun j : J => f ⟨e j,Finset.mem_image_of_mem e j.2⟩
  have hg : Measurable g := by fun_prop
  have hm : Measurable (J.restrict : (ℕ → ℝ) → (J → ℝ)) := by fun_prop
  change (ν.map E).map J.restrict = (μ.map E).map J.restrict
  rw [Measure.map_map hm hE.measurable,Measure.map_map hm hE.measurable]
  have he : J.restrict ∘ E = g ∘ (fun f : C(unitInterval,ℝ) => I.restrict f) := rfl
  rw [he,← Measure.map_map hg (continuous_path_restrict I).measurable,
    ← Measure.map_map hg (continuous_path_restrict I).measurable,h I]

theorem exists_path_limit_of_tight_finite_limit
    (μ : ℕ → ProbabilityMeasure C(unitInterval,ℝ))
    (P : (I : Finset unitInterval) → ProbabilityMeasure (I → ℝ))
    (ht : IsTightMeasureSet (Set.range (fun n => (μ n : Measure C(unitInterval,ℝ)))))
    (hf : ∀ I, Tendsto (fun n => (μ n).map (f := (fun path : C(unitInterval,ℝ) => I.restrict path)) (continuous_path_restrict I).aemeasurable)
      atTop (𝓝 (P I))) :
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ), Tendsto μ atTop (𝓝 W) ∧
      ∀ I, W.map (f := (fun path : C(unitInterval,ℝ) => I.restrict path)) (continuous_path_restrict I).aemeasurable = P I := by
  have hc : IsCompact (closure (Set.range μ)) :=
    isCompact_closure_of_isTightMeasureSet (by
      convert ht using 1
      all_goals try with_reducible_and_instances rfl
      ext x
      simp)
  have hmem n : μ n ∈ closure (Set.range μ) := subset_closure (Set.mem_range_self n)
  obtain ⟨W,_,s,hs,hw⟩ := hc.tendsto_subseq hmem
  have hid : ∀ (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
      (V : ProbabilityMeasure C(unitInterval,ℝ)),
      Tendsto (μ ∘ n) atTop (𝓝 V) →
      ∀ I, V.map (f := (fun path : C(unitInterval,ℝ) => I.restrict path)) (continuous_path_restrict I).aemeasurable = P I := by
    intro n hn V hv I
    exact tendsto_nhds_unique
      ((ProbabilityMeasure.continuous_map (continuous_path_restrict I)).tendsto V |>.comp hv)
      ((hf I).comp hn)
  have hW := hid s hs.tendsto_atTop W hw
  refine ⟨W,?_,hW⟩
  apply Filter.tendsto_of_subseq_tendsto
  intro n hn
  obtain ⟨V,_,s,hs,hv⟩ := hc.tendsto_subseq (fun j => hmem (n j))
  have hV := hid (n ∘ s) (hn.comp hs.tendsto_atTop) V hv
  have he : V = W := by
    have : IsProbabilityMeasure (V : Measure C(unitInterval,ℝ)) := V.prop
    have : IsProbabilityMeasure (W : Measure C(unitInterval,ℝ)) := W.prop
    apply Subtype.ext
    apply continuous_path_measure_ext (V : Measure C(unitInterval,ℝ))
      (W : Measure C(unitInterval,ℝ))
    intro I
    exact congrArg (fun Q : ProbabilityMeasure (I → ℝ) => (Q : Measure (I → ℝ)))
      ((hV I).trans (hW I).symm)
  subst V
  exact ⟨s,hv⟩

theorem gaussian_iid_path_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      TendstoInDistribution (fun i ω => scaledPolygon (fun k => X k ω)
        (r i) (fluctuationScale μ (X 0) (r i)) T) atTop id (fun _ => μ) W ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun f : C(unitInterval,ℝ) => I.restrict f) =
          gaussianPathFiniteLaw T I := by
  let Y := fun i ω => scaledPolygon (fun k => X k ω) (r i)
    (fluctuationScale μ (X 0) (r i)) T
  have hY : ∀ i, Measurable (Y i) := fun _ => measurable_scaledPolygon X hX _ _ _
  let M : ℕ → ProbabilityMeasure C(unitInterval,ℝ) := fun i =>
    ⟨μ.map (Y i),(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  let P : (I : Finset unitInterval) → ProbabilityMeasure (I → ℝ) := fun I =>
    ⟨gaussianPathFiniteLaw T I,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have ht : IsTightMeasureSet (Set.range (fun i => (M i : Measure C(unitInterval,ℝ)))) :=
    gaussian_iid_path_tight μ X hX hind hident hsym hI hne r hr hT
  have hf : ∀ I, Tendsto (fun i => (M i).map (f := fun path : C(unitInterval,ℝ) => I.restrict path) (continuous_path_restrict I).aemeasurable)
      atTop (𝓝 (P I)) := by
    intro I
    have h := (gaussian_polygon_finite_limit μ X hX hind hident hI hne hsym r hr hT I).tendsto
    have he : (fun i => (M i).map (f := fun path : C(unitInterval,ℝ) => I.restrict path) (continuous_path_restrict I).aemeasurable) =
        (fun i => (⟨μ.map (fun ω => I.restrict (Y i ω)),
          (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map ((continuous_path_restrict I).measurable.comp (hY i)).aemeasurable)⟩ :
          ProbabilityMeasure (I → ℝ))) := by
      funext i
      apply Subtype.ext
      exact Measure.map_map (continuous_path_restrict I).measurable (hY i)
    rw [he]
    simpa only [Measure.map_id] using h
  obtain ⟨W,hw,hf⟩ := exists_path_limit_of_tight_finite_limit M P ht hf
  refine ⟨W,⟨fun i => (hY i).aemeasurable,measurable_id.aemeasurable,?_⟩,?_⟩
  · convert hw using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg
    apply Subtype.ext
    exact Measure.map_id
  · intro I
    exact congrArg (fun Q : ProbabilityMeasure (I → ℝ) => (Q : Measure (I → ℝ))) (hf I)

lemma renewalSum_zero (L : ℕ → ℕ) : renewalSum L 0 = 0 := by simp [renewalSum]
lemma renewalSum_succ (L : ℕ → ℕ) (n : ℕ) : renewalSum L (n+1) = renewalSum L n+L n := by
  simp [renewalSum,Finset.sum_range_succ]
lemma renewalSum_ge (L : ℕ → ℕ) (hL : ∀ k, 0 < L k) (n : ℕ) : n ≤ renewalSum L n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => rw [renewalSum_succ]; have := hL n; omega
lemma renewalCount_le (L : ℕ → ℕ) (h : ℕ) : renewalCount L h ≤ h := Nat.findGreatest_le _
lemma renewalCount_lower (L : ℕ → ℕ) (h : ℕ) : renewalSum L (renewalCount L h) ≤ h := by
  classical
  exact Nat.findGreatest_spec (P := fun k => renewalSum L k ≤ h) (Nat.zero_le h)
    (by rw [renewalSum_zero]; exact Nat.zero_le _)
lemma renewalCount_upper (L : ℕ → ℕ) (hL : ∀ k, 0 < L k) (h : ℕ) :
    h < renewalSum L (renewalCount L h+1) := by
  classical
  by_cases hk : renewalCount L h+1 ≤ h
  · exact Nat.lt_of_not_ge (Nat.findGreatest_is_greatest
      (P := fun k => renewalSum L k ≤ h) (Nat.lt_succ_self _) hk)
  · exact (Nat.lt_of_not_ge hk).trans_le (renewalSum_ge L hL _)
lemma renewalCount_zero (L : ℕ → ℕ) : renewalCount L 0 = 0 := by simp [renewalCount]

lemma linear_error_uniform (f : ℕ → ℝ) (c : ℝ)
    (hf : Tendsto (fun k : ℕ => f k/k) atTop (𝓝 c))
    {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ k : ℕ, (k : ℝ) ≤ T*a → |f k-c*k| ≤ ε*a := by
  have hδ : 0 < ε/(T+1) := div_pos hε (by linarith)
  obtain ⟨K,hK⟩ := (Metric.tendsto_atTop.1 hf) (ε/(T+1)) hδ
  let C := ∑ k ∈ Finset.range (K+1), |f k-c*k|
  filter_upwards [eventually_ge_atTop (max 0 (C/ε))] with a ha k hk
  have ha0 : 0 ≤ a := (le_max_left _ _).trans ha
  by_cases hkK : k ≤ K
  · have h1 : |f k-c*k| ≤ C := Finset.single_le_sum (fun j _ => abs_nonneg (f j-c*j))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hkK))
    exact h1.trans (by simpa [mul_comm] using (div_le_iff₀ hε).1 ((le_max_right _ _).trans ha))
  · have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have he : f k/(k : ℝ)-c = (f k-c*k)/k := by field_simp
    have hbound := hK k (by omega)
    rw [Real.dist_eq,he,abs_div,abs_of_pos hkpos] at hbound
    have hh := (div_lt_iff₀ hkpos).1 hbound
    have h2 : (ε/(T+1))*(k : ℝ) ≤ ε*a := by
      calc
        _ ≤ (ε/(T+1))*(T*a) := mul_le_mul_of_nonneg_left hk hδ.le
        _ ≤ ε*a := by
          have hd : T/(T+1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
          calc
            _ = (ε*a)*(T/(T+1)) := by ring
            _ ≤ ε*a := mul_le_of_le_one_right (mul_nonneg hε.le ha0) hd
    exact hh.le.trans h2

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWidthProcess
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma renewalCount_uniform (L : ℕ → ℕ) (hL : ∀ k, 0 < L k) {c : ℝ} (hc : 0 < c)
    (hmean : Tendsto (fun k : ℕ => (renewalSum L k : ℝ)/k) atTop (𝓝 c))
    {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, 0 < a ∧ ∀ h : ℕ, (h : ℝ) ≤ T*a →
      |(renewalCount L h : ℝ)/a-(h : ℝ)/(c*a)| ≤ ε := by
  have hlinear := linear_error_uniform (fun k => (renewalSum L k : ℝ)) c hmean
    (T := T+1) (ε := ε*c/2) (by linarith) (by positivity)
  filter_upwards [hlinear,eventually_ge_atTop (max 1 (2/ε))] with a ha ha'
  have ha1 : 1 ≤ a := (le_max_left _ _).trans ha'
  have ha0 : 0 < a := by linarith
  refine ⟨ha0,fun h hh => ?_⟩
  let k := renewalCount L h
  have hk : (k : ℝ) ≤ T*a := (Nat.cast_le.2 (renewalCount_le L h)).trans hh
  have hk' : (k+1 : ℝ) ≤ (T+1)*a := by linarith
  have haK := ha k (by nlinarith : (k : ℝ) ≤ (T+1)*a)
  have haK' := ha (k+1) (by simpa using hk')
  have hlo : (renewalSum L k : ℝ) ≤ (h : ℝ) := by exact_mod_cast renewalCount_lower L h
  have hup : (h : ℝ) < (renewalSum L (k+1) : ℝ) := by exact_mod_cast renewalCount_upper L hL h
  have hbig : 2 ≤ ε*a := by simpa [mul_comm] using (div_le_iff₀ hε).1 ((le_max_right _ _).trans ha')
  have he : (k : ℝ)/a-(h : ℝ)/(c*a) = (c*k-h)/(c*a) := by field_simp
  rw [he,abs_div,abs_of_pos (mul_pos hc ha0),div_le_iff₀ (mul_pos hc ha0)]
  rcases abs_le.mp haK with ⟨haK1,haK2⟩
  rcases abs_le.mp haK' with ⟨haK1',haK2'⟩
  push_cast at haK1' haK2'
  apply abs_le.2
  constructor <;> nlinarith

lemma measurable_renewalCount {Ω : Type*} [MeasurableSpace Ω]
    (L : ℕ → Ω → ℕ) (hL : ∀ k, Measurable (L k)) (h : ℕ) :
    Measurable (fun ω => renewalCount (fun k => L k ω) h) := by
  classical
  apply measurable_findGreatest
  intro k _
  exact measurableSet_le (Finset.measurable_sum _ (fun j _ => hL j)) measurable_const

lemma measure_tendsto_zero_of_ae_eventually_notMem {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : ℕ → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (he : ∀ᵐ ω ∂μ, ∀ᶠ i in atTop, ω ∉ A i) :
    Tendsto (fun i => μ (A i)) atTop (𝓝 0) := by
  let F := fun i => (A i).indicator (fun _ => (1 : ℝ))
  have hF : ∀ i, Measurable (F i) := fun i => measurable_const.indicator (hA i)
  have hc : TendstoInMeasure μ F atTop 0 := by
    apply tendstoInMeasure_of_tendsto_ae (fun i => (hF i).aestronglyMeasurable)
    filter_upwards [he] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with i hi
    simp [F,hi]
  have h := (tendstoInMeasure_iff_norm.1 hc) 1 zero_lt_one
  have hi : ∀ i, {ω | (1:ℝ) ≤ ‖F i ω-(0 : Ω → ℝ) ω‖} = A i := by
    intro i
    ext ω
    by_cases hω : ω ∈ A i <;> simp [F,hω]
  simpa only [hi] using h

lemma renewalCount_uniform_in_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (L : ℕ → Ω → ℕ)
    (hL : ∀ k, Measurable (L k)) (hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < L k ω)
    {c : ℝ} (hc : 0 < c)
    (hmean : ∀ᵐ ω ∂μ, Tendsto (fun k : ℕ => (renewalSum (fun j => L j ω) k : ℝ)/k)
      atTop (𝓝 c)) (n : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    Tendsto (fun i => μ {ω | ∃ h : ℕ, (h : ℝ) ≤ T*n i ∧
      ε < |(renewalCount (fun j => L j ω) h : ℝ)/n i-(h : ℝ)/(c*n i)|}) atTop (𝓝 0) := by
  apply measure_tendsto_zero_of_ae_eventually_notMem
  · intro i
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro h
    exact (MeasurableSet.const _).inter
      (measurableSet_lt measurable_const ((((measurable_of_countable (fun j : ℕ => (j : ℝ))).comp (measurable_renewalCount L hL h)).div_const _).sub
        measurable_const).abs)
  · filter_upwards [hpos,hmean] with ω hpos hmean
    have h := hn.eventually (renewalCount_uniform (fun j => L j ω) hpos hc hmean hT hε)
    filter_upwards [h] with i hi
    rintro ⟨h,hh,hbad⟩
    exact (not_lt_of_ge (hi.2 h hh)) hbad

lemma renewalReward_sum (x : ℕ → ℝ) (L : ℕ → ℕ) (h : ℕ) :
    realPartialSum (renewalRewardIncrement x L) h = realPartialSum x (renewalCount L h) := by
  induction h with
  | zero => simp [realPartialSum,renewalCount_zero]
  | succ h ih => rw [realPartialSum_succ,ih,renewalRewardIncrement]; ring

lemma measurable_nat_select {Ω : Type*} [MeasurableSpace Ω] (F : ℕ → Ω → ℝ)
    (hF : ∀ k, Measurable (F k)) (k : Ω → ℕ) (hk : Measurable k) :
    Measurable (fun ω => F (k ω) ω) :=
  (measurable_from_prod_countable_left (f := fun p : Ω × ℕ => F p.2 p.1) (fun j => hF j)).comp (measurable_id.prodMk hk)

lemma measurable_renewalRewardIncrement {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (L : ℕ → Ω → ℕ) (hX : ∀ k, Measurable (X k))
    (hL : ∀ k, Measurable (L k)) (h : ℕ) :
    Measurable (fun ω => renewalRewardIncrement (fun k => X k ω) (fun k => L k ω) h) := by
  exact (measurable_nat_select _ (measurable_realPartialSum X hX) _
    (measurable_renewalCount L hL (h+1))).sub
      (measurable_nat_select _ (measurable_realPartialSum X hX) _ (measurable_renewalCount L hL h))

lemma abs_convex_sub_le {a b z q A : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ha : |a-z| ≤ A) (hb : |b-z| ≤ A) : |(1-q)*a+q*b-z| ≤ A := by
  have he : (1-q)*a+q*b-z = (1-q)*(a-z)+q*(b-z) := by ring
  rw [he]
  calc
    _ ≤ |(1-q)*(a-z)|+|q*(b-z)| := abs_add_le _ _
    _ = (1-q)*|a-z|+q*|b-z| := by rw [abs_mul,abs_mul,abs_of_nonneg hq,abs_of_nonneg (by linarith : 0 ≤ 1-q)]
    _ ≤ (1-q)*A+q*A := add_le_add (mul_le_mul_of_nonneg_left ha (by linarith))
      (mul_le_mul_of_nonneg_left hb hq)
    _ = A := by ring

lemma renewalRewardPolygon_close {Ω : Type*} (X : ℕ → Ω → ℝ) (L : ℕ → Ω → ℕ) (ω : Ω)
    {r n T c δ ε : ℝ} (hr : 0 < r) (hn : 1 ≤ n) (hT : 0 ≤ T)
    (hc : 1 ≤ c) (_hδ : 0 < δ) (hδn : 8 ≤ δ*n)
    (hclock : ∀ h : ℕ, (h : ℝ) ≤ (T+1)*n →
      |(renewalCount (fun k => L k ω) h : ℝ)/n-(h : ℝ)/(c*n)| ≤ δ/4)
    (hgrid : ω ∉ GridOscillation X ⌊(T+2)*n⌋₊ ⌊δ*n⌋₊ (ε*r)) :
    ‖scaledPolygon (renewalRewardIncrement (fun k => X k ω) (fun k => L k ω)) r n T-
      scaledPolygon (fun k => X k ω) r n (T/c)‖ ≤ 2*ε := by
  have hn0 : 0 < n := by linarith
  have hc0 : 0 < c := by linarith
  have hTn : 0 ≤ T*n := mul_nonneg hT hn0.le
  have hTc : 0 ≤ T/c := div_nonneg hT hc0.le
  apply (ContinuousMap.norm_le_of_nonempty _).mpr
  intro t
  let u := T*n*(t : ℝ)
  let v := (T/c)*n*(t : ℝ)
  let j := ⌊u⌋₊
  let k := ⌊v⌋₊
  let S := realPartialSum (fun l => X l ω)
  let C := renewalCount (fun l => L l ω)
  have hu : 0 ≤ u := mul_nonneg hTn t.2.1
  have huT : u ≤ T*n := mul_le_of_le_one_right hTn t.2.2
  have hv : 0 ≤ v := mul_nonneg (mul_nonneg hTc hn0.le) t.2.1
  have huv : v = u/c := by dsimp [u,v] <;> ring
  have hvu : v ≤ u := by rw [huv]; exact div_le_self hu hc
  have hj : (j : ℝ) ≤ u := Nat.floor_le hu
  have hj' : u < (j : ℝ)+1 := Nat.lt_floor_add_one u
  have hk : (k : ℝ) ≤ v := Nat.floor_le hv
  have hk' : v < (k : ℝ)+1 := Nat.lt_floor_add_one v
  have hjH : ∀ h : ℕ, (h : ℝ) ≤ (j : ℝ)+1 → (h : ℝ) ≤ (T+1)*n := by
    intro h hh
    nlinarith
  have hH : 1 ≤ ⌊δ*n⌋₊ := by apply Nat.le_floor; norm_num <;> linarith
  have hkN : k+1 ≤ ⌊(T+2)*n⌋₊ := by apply Nat.le_floor; push_cast <;> nlinarith
  have hb : ∀ h : ℕ, |(h : ℝ)-u| ≤ 1 → (h : ℝ) ≤ (j : ℝ)+1 →
      |S (C h)-S k| ≤ ε*r := by
    intro h hhu hhj
    have hhN : C h ≤ ⌊(T+2)*n⌋₊ := by
      apply (renewalCount_le _ _).trans
      apply Nat.le_floor
      have := hjH h hhj
      nlinarith
    have he := hclock h (hjH h hhj)
    have hcV : |(C h : ℝ)-v| ≤ δ*n/2 := by
      have hrw : ((C h : ℝ)/n-(h : ℝ)/(c*n))*n = (C h : ℝ)-(h : ℝ)/c := by
        dsimp [C]; field_simp
      have hb := mul_le_mul_of_nonneg_right he hn0.le
      change |(C h : ℝ)/n-(h : ℝ)/(c*n)| *n ≤ δ/4*n at hb
      have heq : |((C h : ℝ)/n-(h : ℝ)/(c*n))*n| =
          |(C h : ℝ)/n-(h : ℝ)/(c*n)| *n := by rw [abs_mul,abs_of_pos hn0]
      rw [← heq,hrw] at hb
      have he2 : |(h : ℝ)/c-v| ≤ 1 := by
        rw [huv,← sub_div,abs_div,abs_of_pos hc0]
        apply (div_le_iff₀ hc0).2
        simpa using hhu.trans hc
      have ht := abs_add_le ((C h : ℝ)-(h : ℝ)/c) ((h : ℝ)/c-v)
      have he3 : (C h : ℝ)-v = ((C h : ℝ)-(h : ℝ)/c)+((h : ℝ)/c-v) := by ring
      rw [← he3] at ht
      dsimp [C] at hb ⊢
      nlinarith
    have hnear := floor_scaled_close (Nat.cast_nonneg (C h)) hv (by linarith : 4 ≤ δ*n) hcV
    have hnear' := floor_scaled_close hv (Nat.cast_nonneg (C h)) (by linarith : 4 ≤ δ*n)
      (by simpa [abs_sub_comm] using hcV)
    simp only [Nat.floor_natCast] at hnear hnear'
    exact not_gridOscillation_bound X hgrid (by omega) hhN hnear' hnear
  have hb0 := hb j (by apply abs_le.2; constructor <;> linarith) (by linarith)
  have hb1 := hb (j+1) (by push_cast; apply abs_le.2; constructor <;> linarith) (by push_cast; rfl)
  have hpoly := abs_convex_sub_le (q := u-j) (by linarith) (by linarith) hb0 hb1
  have hpN : j < ⌊T*n⌋₊+1 := Nat.lt_succ_of_le (Nat.floor_mono huT)
  have hqN : k < ⌊(T/c)*n⌋₊+1 := Nat.lt_succ_of_le
    (Nat.floor_mono (mul_le_of_le_one_right (mul_nonneg hTc hn0.le) t.2.2))
  have hpolyEq : linearPolygon (renewalRewardIncrement (fun l => X l ω) (fun l => L l ω))
      (⌊T*n⌋₊+1) u = (1-(u-j))*S (C j)+(u-j)*S (C (j+1)) := by
    rw [linearPolygon_formula _ _ hu hpN,renewalReward_sum,renewalRewardIncrement]
    dsimp [j,S,C]
    ring
  rw [← hpolyEq] at hpoly
  have hx : |X k ω| ≤ ε*r := by
    rw [← realPartialSum_step (fun l => X l ω)]
    exact not_gridOscillation_bound X hgrid (by omega) hkN (by omega) (by omega)
  have hdet := linearPolygon_near_partialSum (x := fun l => X l ω) hv hqN hx
  change |linearPolygon (fun l => X l ω) (⌊(T/c)*n⌋₊+1) v-S k| ≤ ε*r at hdet
  have hfin := (abs_sub_le _ (S k) _).trans (add_le_add hpoly (by simpa [abs_sub_comm] using hdet))
  simp only [ContinuousMap.sub_apply,Real.norm_eq_abs,scaledPolygon_apply]
  rw [← sub_div,abs_div,abs_of_pos hr]
  apply (div_le_iff₀ hr).2
  convert hfin using 1 <;> first | rfl | ring

lemma gaussian_renewal_path_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (L : ℕ → Ω → ℕ) (hL : ∀ k, Measurable (L k))
    (hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < L k ω) {c : ℝ} (hc : 1 ≤ c)
    (hmean : ∀ᵐ ω ∂μ, Tendsto (fun k : ℕ => (renewalSum (fun j => L j ω) k : ℝ)/k)
      atTop (𝓝 c)) (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T : ℝ} (hT : 0 ≤ T) :
    TendstoInMeasure μ (fun i ω =>
      scaledPolygon (renewalRewardIncrement (fun k => X k ω) (fun k => L k ω))
        (r i) (fluctuationScale μ (X 0) (r i)) T-
      scaledPolygon (fun k => X k ω) (r i) (fluctuationScale μ (X 0) (r i)) (T/c)) atTop 0 := by
  let n := fun i => fluctuationScale μ (X 0) (r i)
  have hn : Tendsto n atTop atTop := (fluctuationScale_tendsto μ (X 0) (hX 0) hI hne).comp hr.1
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  simp only [Pi.zero_apply,sub_zero]
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
  · intro β hβ
    obtain ⟨δ,hδ,hgrid⟩ := gaussian_grid_modulus μ X hX hind hident hsym hI hne r hr
      (by linarith : 0 ≤ T+2) (by linarith : 0 < ε/4) (by linarith : 0 < β/3)
    let A := fun i => {ω | ∃ h : ℕ, (h : ℝ) ≤ (T+1)*n i ∧
      δ/4 < |(renewalCount (fun j => L j ω) h : ℝ)/n i-(h : ℝ)/(c*n i)|}
    have hclock := renewalCount_uniform_in_probability μ L hL hpos
      (by linarith : 0 < c) hmean n hn (by linarith : 0 ≤ T+1) (by linarith : 0 < δ/4)
    have hclock' : Tendsto (fun i => μ.real (A i)) atTop (𝓝 0) := by
      convert (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞) ≠ ⊤)).comp hclock using 1 <;>
        simp [Function.comp_def,Measure.real,A]
    have hb := (tendsto_order.mp hclock').2 (β/3) (by linarith)
    filter_upwards [hgrid,hb,hr.1.eventually (eventually_gt_atTop (0:ℝ)),
      hn.eventually (eventually_ge_atTop (1:ℝ)),
      (hn.const_mul_atTop hδ).eventually (eventually_ge_atTop (8:ℝ))]
      with i hg ha hri hni hdni
    let B := GridOscillation X ⌊(T+2)*n i⌋₊ ⌊δ*n i⌋₊ ((ε/4)*r i)
    have hs : {ω | ε ≤ ‖scaledPolygon (renewalRewardIncrement (fun k => X k ω)
        (fun k => L k ω)) (r i) (n i) T-
        scaledPolygon (fun k => X k ω) (r i) (n i) (T/c)‖} ⊆ A i ∪ B := by
      intro ω hω
      by_contra hnot
      have hnot : ω ∉ A i ∧ ω ∉ B := by simpa only [Set.mem_union,not_or] using hnot
      have hclockdet : ∀ h : ℕ, (h : ℝ) ≤ (T+1)*n i →
          |(renewalCount (fun k => L k ω) h : ℝ)/n i-(h : ℝ)/(c*n i)| ≤ δ/4 := by
        intro h hh
        exact le_of_not_gt (fun hh' => hnot.1 ⟨h,hh,hh'⟩)
      have hd := renewalRewardPolygon_close X L ω hri hni hT hc hδ hdni hclockdet hnot.2
      simp only [Set.mem_ofPred_eq] at hω
      linarith
    have hm := (measureReal_mono (μ := μ) hs (measure_ne_top _ _)).trans
      (measureReal_union_le (μ := μ) (A i) B)
    change μ.real B ≤ β/3 at hg
    exact hm.trans_lt (by linarith)

theorem gaussian_renewal_path_limit_oai {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (L : ℕ → Ω → ℕ) (hL : ∀ k, Measurable (L k))
    (hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < L k ω) {c : ℝ} (hc : 1 ≤ c)
    (hmean : ∀ᵐ ω ∂μ, Tendsto (fun k : ℕ => (renewalSum (fun j => L j ω) k : ℝ)/k)
      atTop (𝓝 c)) (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      TendstoInDistribution (fun i ω => scaledPolygon
        (renewalRewardIncrement (fun k => X k ω) (fun k => L k ω))
        (r i) (fluctuationScale μ (X 0) (r i)) T) atTop id (fun _ => μ) W ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun f : C(unitInterval,ℝ) => I.restrict f) =
          gaussianPathFiniteLaw (T/c) I := by
  obtain ⟨W,hW,hf⟩ := gaussian_iid_path_limit μ X hX hind hident hsym hI hne r hr
    (div_nonneg hT (by linarith : 0 ≤ c))
  refine ⟨W,?_,hf⟩
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ id hW
  · exact gaussian_renewal_path_error μ X hX hind hident hsym hI hne L hL hpos hc hmean r hr hT
  · intro i
    exact (measurable_scaledPolygon _ (measurable_renewalRewardIncrement X L hX hL) _ _ _).aemeasurable

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DirectionalTransience.gaussian_renewal_path_limit_oai.{u_1} := @OAI.DirectionalTransience.gaussian_renewal_path_limit_oai.{u_1}
