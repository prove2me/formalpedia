-- Prove2me | solution 1 for OAI.Invariant233.CircleCoupling.tail_exceptional_families_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:54.410832+00:00
-- url     : https://prove2.me/submissions/7e2fd595-feda-44e6-af5f-2172eb5db077

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003
import Theorems.Thm_OAI_Invariant233_CircleCoupling_actual_tail_attenuation_of_ac_order
import Theorems.Thm_OAI_Invariant233_CircleCoupling_endpoint_absolutelyContinuous

section
-- module Solutions.Q234_IR.Compat
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_UniformQuantization
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.UniformQuantization

theorem quantize_eq_iff {q : ℕ} [NeZero q] (a : Fin q) {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) :
    quantize q x = a ↔ x ∈ Ico ((a : ℝ) / q) (((a : ℝ) + 1) / q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hnonneg : 0 ≤ (q : ℝ) * x := mul_nonneg hq.le hx.1
  have hfloor : ⌊(q : ℝ) * x⌋₊ < q := (Nat.floor_lt hnonneg).mpr (by nlinarith [hx.2])
  change (⟨⌊(q : ℝ) * x⌋₊ % q, _⟩ : Fin q) = a ↔ _
  rw [Fin.ext_iff]
  change (⌊(q : ℝ) * x⌋₊ % q = a.val) ↔ _
  rw [Nat.mod_eq_of_lt hfloor, Nat.floor_eq_iff hnonneg]
  simp only [mem_Ico]
  constructor
  · intro h
    exact ⟨(div_le_iff₀ hq).mpr (by nlinarith [h.1]),
      (lt_div_iff₀ hq).mpr (by nlinarith [h.2])⟩
  · intro h
    constructor
    · have := (div_le_iff₀ hq).mp h.1
      nlinarith
    · have := (lt_div_iff₀ hq).mp h.2
      nlinarith

theorem preimage_singleton_inter_unit {q : ℕ} [NeZero q] (a : Fin q) :
    (quantize q ⁻¹' {a}) ∩ Ico (0 : ℝ) 1 =
      Ico ((a : ℝ) / q) (((a : ℝ) + 1) / q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  ext x
  constructor
  · rintro ⟨hxa, hx⟩
    exact (quantize_eq_iff a hx).mp hxa
  · intro hx
    have hunit : x ∈ Ico (0 : ℝ) 1 := by
      constructor
      · exact (div_nonneg (by positivity) hq.le).trans hx.1
      · have ha : (a : ℝ) + 1 ≤ q := by exact_mod_cast Nat.succ_le_of_lt a.isLt
        have hbound : ((a : ℝ) + 1) / q ≤ 1 := (div_le_iff₀ hq).mpr (by linarith)
        exact hx.2.trans_le hbound
    exact ⟨(quantize_eq_iff a hunit).mpr hx, hunit⟩

theorem map_quantize_singleton (q : ℕ) [NeZero q] (a : Fin q) :
    (volume.restrict (Ico (0 : ℝ) 1)).map (quantize q) {a} = (q : ℝ≥0∞)⁻¹ := by
  rw [Measure.map_apply (measurable_quantize q) (measurableSet_singleton a),
    Measure.restrict_apply ((measurable_quantize q) (measurableSet_singleton a)),
    preimage_singleton_inter_unit, Real.volume_Ico]
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have heq : ((a : ℝ) + 1) / q - (a : ℝ) / q = 1 / q := by ring
  rw [heq, ENNReal.ofReal_div_of_pos hq]
  simp

end Invariant233.UniformQuantization

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadix
attribute [-instance] _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.MixedRadix.hybrid_apply_ge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.MixedRadix

theorem sum_terms_le_reciprocal_gap {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (j N : ℕ) :
    (∑ n ∈ Finset.range N, term d (j + n)) ≤
      1 / (denominator r j : ℝ) - 1 / (denominator r (j + N) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hterm := term_le_reciprocal_gap hr d (j + N)
      simp only [Nat.add_assoc] at hterm
      linarith

theorem summable_terms {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) :
    Summable (term d) := by
  apply summable_of_sum_range_le (term_nonneg d) (c := 1)
  intro N
  have h := sum_terms_le_reciprocal_gap hr d 0 N
  simp only [Nat.zero_add, denominator_zero, Nat.cast_one, div_one] at h
  have hnonneg : (0 : ℝ) ≤ 1 / (denominator r N : ℝ) := by positivity
  linarith

theorem tsum_tail_le {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) (j : ℕ) :
    (∑' n, term d (j + n)) ≤ 1 / (denominator r j : ℝ) := by
  apply Real.tsum_le_of_sum_range_le (fun n => term_nonneg d (j + n))
  intro N
  have h := sum_terms_le_reciprocal_gap hr d j N
  have hnonneg : (0 : ℝ) ≤ 1 / (denominator r (j + N) : ℝ) := by positivity
  linarith

theorem tailValue_nonneg {r : ℕ → ℕ} (d : Digits r) (j : ℕ) :
    0 ≤ tailValue d j := by
  unfold tailValue
  exact mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg (fun n => term_nonneg d (j + n)))

theorem tailValue_le_one {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) (j : ℕ) :
    tailValue d j ≤ 1 := by
  have hq : (0 : ℝ) < denominator r j := by exact_mod_cast denominator_pos hr j
  calc
    tailValue d j ≤ (denominator r j : ℝ) * (1 / (denominator r j : ℝ)) :=
      mul_le_mul_of_nonneg_left (tsum_tail_le hr d j) hq.le
    _ = 1 := by field_simp

theorem tailValue_mono {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) {d e : Digits r}
    (hde : ∀ n, d n ≤ e n) (j : ℕ) : tailValue d j ≤ tailValue e j := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply ((summable_terms hr d).comp_injective (fun _ _ h => Nat.add_left_cancel h)).tsum_le_tsum
    _ ((summable_terms hr e).comp_injective (fun _ _ h => Nat.add_left_cancel h))
  intro n
  exact div_le_div_of_nonneg_right (by exact_mod_cast hde (j + n)) (Nat.cast_nonneg _)

theorem tailValue_rec {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) (j : ℕ) :
    tailValue d j = ((d j : ℝ) + tailValue d (j + 1)) / (r j : ℝ) := by
  have hs : Summable (fun n => term d (j + (n + 1))) :=
    (summable_terms hr d).comp_injective (fun _ _ h => by omega)
  have hsplit : (∑' n, term d (j + n)) =
      term d j + ∑' n, term d (j + 1 + n) := by
    simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using tsum_eq_zero_add' (f := fun n => term d (j + n)) hs
  have hq : (denominator r j : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast denominator_pos hr j)
  have hrr : (r j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr j)
  unfold tailValue
  rw [hsplit]
  simp only [term, denominator_succ, Nat.cast_mul]
  field_simp

theorem ofDigits_eq_prefix_add_tail {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (N : ℕ) :
    ofDigits d = (∑ n ∈ Finset.range N, term d n) + ∑' n, term d (N + n) := by
  simpa only [ofDigits, Nat.add_comm] using
    ((summable_terms hr d).sum_add_tsum_nat_add N).symm

theorem denominator_mul_prefix {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (N : ℕ) :
    (denominator r N : ℝ) * (∑ n ∈ Finset.range N, term d n) = (prefixRank d N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hq : (denominator r N : ℝ) ≠ 0 :=
        ne_of_gt (by exact_mod_cast denominator_pos hr N)
      have hrr : (r N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr N)
      rw [Finset.sum_range_succ, prefixRank_succ, Nat.cast_add, Nat.cast_mul]
      simp only [term, denominator_succ, Nat.cast_mul] at *
      field_simp at *
      nlinarith

theorem denominator_mul_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (N : ℕ) :
    (denominator r N : ℝ) * ofDigits d = (prefixRank d N : ℝ) + tailValue d N := by
  rw [ofDigits_eq_prefix_add_tail hr d N, mul_add, denominator_mul_prefix hr d N]
  rfl

theorem tailValue_eq_one_imp_next {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (j : ℕ) (heq : tailValue d j = 1) :
    tailValue d (j + 1) = 1 := by
  have hrr : (r j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr j)
  have hrec := (eq_div_iff hrr).mp (tailValue_rec hr d j)
  have hd : (d j : ℝ) + 1 ≤ (r j : ℝ) := by exact_mod_cast (d j).isLt
  rw [heq, one_mul] at hrec
  linarith [tailValue_le_one hr d (j + 1)]

theorem tailValue_lt_one {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) (j : ℕ) : tailValue d j < 1 := by
  by_contra hnot
  have heq : tailValue d j = 1 := le_antisymm (tailValue_le_one hr d j) (le_of_not_gt hnot)
  have hprop : ∀ k, tailValue d (j + k) = 1 := by
    intro k
    induction k with
    | zero => simpa using heq
    | succ k ih =>
        simpa only [Nat.add_assoc] using tailValue_eq_one_imp_next hr d (j + k) ih
  obtain ⟨n, hjn, hn⟩ := hnt j
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hjn
  have hrr : (r (j + k) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr (j + k))
  have hrec := (eq_div_iff hrr).mp (tailValue_rec hr d (j + k))
  rw [hprop k, one_mul] at hrec
  have hd : (d (j + k) : ℝ) + 1 < (r (j + k) : ℝ) := by exact_mod_cast hn
  linarith [tailValue_le_one hr d (j + k + 1)]

theorem fract_denominator_mul_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) (j : ℕ) :
    Int.fract ((denominator r j : ℝ) * ofDigits d) = tailValue d j := by
  rw [denominator_mul_ofDigits hr d j, Int.fract_natCast_add]
  exact Int.fract_eq_self.mpr ⟨tailValue_nonneg d j, tailValue_lt_one hr d hnt j⟩

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixCircle
attribute [-instance] _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.MixedRadix

theorem denominator_radices {q : ℕ → ℕ} (hq0 : q 0 = 1)
    (hdiv : ∀ n, q n ∣ q (n + 1)) (N : ℕ) : denominator (radices q) N = q N := by
  induction N with
  | zero => simpa using hq0.symm
  | succ N ih =>
      rw [denominator_succ, ih, radices]
      exact Nat.mul_div_cancel' (hdiv N)

theorem radices_pos {q : ℕ → ℕ} (hq : ∀ n, 0 < q n)
    (hstrict : StrictMono q) (hdiv : ∀ n, q n ∣ q (n + 1)) (n : ℕ) :
    0 < radices q n := lt_of_lt_of_le (by decide) (radices_ge_two hq hstrict hdiv n)

theorem coordinate_eq_tailValue {q : ℕ → ℕ} (hq0 : q 0 = 1)
    (hq : ∀ n, 0 < q n) (hstrict : StrictMono q) (hdiv : ∀ n, q n ∣ q (n + 1))
    (d : Digits (radices q)) (hnt : Nonterminal d) (i : ℕ) :
    Int.fract ((q i : ℝ) * ofDigits d) = tailValue d i := by
  rw [← denominator_radices hq0 hdiv i]
  exact fract_denominator_mul_ofDigits (radices_pos hq hstrict hdiv) d hnt i

@[simp] theorem hybrid_apply_lt {r : ℕ → ℕ} (d e : Digits r) {N n : ℕ} (hn : n < N) :
    hybrid d e N n = e n := ite_eq_left hn

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingParameters
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma coupling_K_ge (j : ℕ) (hj : 1 ≤ j) : 100 ≤ p.K j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
  induction n with
  | zero => simpa using hp.initial_K.ge
  | succ n ih =>
    have h := hp.K_double (1 + n) (by omega)
    have he : 1 + (n + 1) = 1 + n + 1 := by omega
    rw [he]
    omega

lemma coupling_radix_ge_N {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) :
    p.N s ≤ (MixedRadix.radices p.q i : ℝ) := by
  simpa only [MixedRadix.radices, Nat.cast_div (hp.frequency_divisible i)
    (by exact_mod_cast (Nat.ne_of_gt (hp.q_pos i)) : (p.q i : ℝ) ≠ 0)] using hp.frequency_ratios s hs i hi

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CouplingMarginalBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Invariant233.CouplingMarginalBounds

lemma rho_div_width_le {κ m w : ℝ} (hκ : 0 ≤ κ)
    (hm : 0 < m) (hw : 1 / m ≤ w) : rho κ m w / w ≤ κ := by
  exact (div_le_iff₀ (width_pos hm hw)).2 (rho_le_mul_width hκ hm hw)

end Invariant233.CouplingMarginalBounds

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CouplingMixture
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace Invariant233.CouplingMixture

variable {X I : Type*} [MeasurableSpace X] [Fintype I]

lemma withDensity_finite_mixture (μ : Measure X) (q : ℝ≥0∞)
    (p : I → ℝ≥0∞) (g : I → X → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    μ.withDensity (fun x => q + ∑ i, p i * g i x) =
      q • μ + ∑ i, p i • μ.withDensity (g i) := by
  classical
  have hsum : μ.withDensity (fun x => ∑ i, p i * g i x) =
      ∑ i, p i • μ.withDensity (g i) := by
    have hfin : ∀ s : Finset I, μ.withDensity (fun x => ∑ i ∈ s, p i * g i x) =
        ∑ i ∈ s, p i • μ.withDensity (g i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        rw [show (fun x => p a * g a x + ∑ i ∈ s, p i * g i x) =
          (fun x => p a * g a x) + (fun x => ∑ i ∈ s, p i * g i x) from rfl,
          withDensity_add_left (show Measurable (fun x => p a * g a x) from measurable_const.mul (hg a)), ih]
        congr 1
        exact withDensity_smul (p a) (hg a)
    exact hfin Finset.univ
  rw [show (fun x => q + ∑ i, p i * g i x) =
    (fun _ => q) + (fun x => ∑ i, p i * g i x) from rfl,
    withDensity_add_left measurable_const, withDensity_const, hsum]

lemma intervalLaw_ae_mem (a b : ℝ) : ∀ᵐ x ∂intervalLaw a b, x ∈ Ico a b :=
  ae_cond_mem measurableSet_Ico

lemma intervalLaw_pair_ordered {a b c d : ℝ} (hbc : b ≤ c) :
    ∀ᵐ z ∂(intervalLaw a b).prod (intervalLaw c d), z.1 ≤ z.2 := by
  have : IsZeroOrProbabilityMeasure (intervalLaw a b) := inferInstanceAs
    (IsZeroOrProbabilityMeasure (volume[|Ico a b]))
  have : IsZeroOrProbabilityMeasure (intervalLaw c d) := inferInstanceAs
    (IsZeroOrProbabilityMeasure (volume[|Ico c d]))
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_fst measurable_snd)]
  filter_upwards [intervalLaw_ae_mem a b] with x hx
  filter_upwards [intervalLaw_ae_mem c d] with y hy
  exact hx.2.le.trans (hbc.trans hy.1)

lemma cond_eq_withDensity_uniformDensity {μ : Measure X} [IsFiniteMeasure μ]
    {s : Set X} (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    μ[|s] = μ.withDensity (fun x =>
      ENNReal.ofReal (CouplingMarginalBounds.uniformDensity μ s x)) := by
  have hc : ENNReal.ofReal ((μ.real s)⁻¹) = (μ s)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hpos, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ s)]
  have hfun : (fun x => ENNReal.ofReal (CouplingMarginalBounds.uniformDensity μ s x)) =
      s.indicator (fun _ => (μ s)⁻¹) := by
    ext x
    by_cases hx : x ∈ s <;> simp [CouplingMarginalBounds.uniformDensity, hx, hc]
  rw [hfun, withDensity_indicator hs, withDensity_const]
  rfl

omit [MeasurableSpace X] in
lemma ofReal_mixture_density (q : ℝ) (p : I → ℝ) (g : I → X → ℝ)
    (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i) (hg : ∀ i x, 0 ≤ g i x) (x : X) :
    ENNReal.ofReal (q + ∑ i, p i * g i x) =
      ENNReal.ofReal q + ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (g i x) := by
  rw [ENNReal.ofReal_add hq (Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (hg i x))),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hp i) (hg i x))]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => ENNReal.ofReal_mul (hp i))

end Invariant233.CouplingMixture

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_OneCoordinateCoupling
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.OneCoordinateCoupling

open CouplingMarginalBounds CouplingMixture

lemma replacement_ae_ordered {m a b : ℝ} (hm : 2 ≤ m) (i : Fin 5) :
    ∀ᵐ z ∂(leftLaw m a b i).prod (rightLaw m a b i), z.1 ≤ z.2 := by
  have hm0 : 0 < m := by linarith
  have hinv : 1 / m ≤ 1 / 2 := by
    apply (div_le_iff₀ hm0).2
    linarith
  fin_cases i <;>
    simp only [leftLaw, rightLaw]
  all_goals apply intervalLaw_pair_ordered
  all_goals linarith

lemma baseLaw_eq_restrict : baseLaw = volume.restrict (Ico (0 : ℝ) 1) := by
  simp [baseLaw, intervalLaw, ProbabilityTheory.cond, Real.volume_Ico]

lemma interval_subset_unit {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    Ico a b ⊆ Ico (0 : ℝ) 1 := by
  intro x hx
  exact ⟨ha.trans hx.1, hx.2.trans_le hb⟩

lemma baseLaw_interval_measure {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    baseLaw.real (Ico a b) = b - a := by
  rw [measureReal_def, baseLaw_eq_restrict, Measure.restrict_apply measurableSet_Ico,
    inter_eq_left.mpr (interval_subset_unit ha hb), Real.volume_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma intervalLaw_eq_base_cond {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    intervalLaw a b = baseLaw[|Ico a b] := by
  rw [baseLaw_eq_restrict]
  simp only [intervalLaw, ProbabilityTheory.cond,
    Measure.restrict_apply measurableSet_Ico,
    Measure.restrict_restrict measurableSet_Ico,
    inter_eq_left.mpr (interval_subset_unit ha hb)]

lemma intervalLaw_eq_base_withDensity {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    intervalLaw a b = baseLaw.withDensity (fun x =>
      ENNReal.ofReal (uniformDensity baseLaw (Ico a b) x)) := by
  rw [intervalLaw_eq_base_cond ha hb]
  apply cond_eq_withDensity_uniformDensity measurableSet_Ico
  rw [baseLaw_interval_measure ha hb hab.le]
  exact sub_pos.mpr hab

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_OneCoordinateDensity
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.OneCoordinateCoupling

open CouplingMarginalBounds CouplingMixture

lemma intervalDensity_measurable (a b : ℝ) : Measurable (intervalDensity a b) :=
  measurable_const.indicator measurableSet_Ico

lemma intervalDensity_nonneg (a b x : ℝ) : 0 ≤ intervalDensity a b x := by
  by_cases hx : x ∈ Ico a b
  · simp [intervalDensity, uniformDensity, hx, inv_nonneg.mpr (measureReal_nonneg)]
  · simp [intervalDensity, uniformDensity, hx]

lemma intervalDensity_le_inv_length {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) (x : ℝ) :
    intervalDensity a b x ≤ (b - a)⁻¹ := by
  by_cases hx : x ∈ Ico a b
  · simp [intervalDensity, uniformDensity, hx, baseLaw_interval_measure ha hb hab.le]
  · simp [intervalDensity, uniformDensity, hx, inv_nonneg.mpr (sub_nonneg.mpr hab.le)]

lemma intervalDensity_le_width {a b w : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hw : 0 < w) (hlen : w / 2 ≤ b - a) (x : ℝ) :
    intervalDensity a b x ≤ 2 / w := by
  have hab : a < b := by linarith
  apply (intervalDensity_le_inv_length ha hb hab x).trans
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (sub_pos.mpr hab) hw).2
  linarith

lemma leftLaw_eq_withDensity {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    leftLaw m a b i = baseLaw.withDensity (fun x => ENNReal.ofReal (leftDensity m a b i x)) := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [leftLaw, leftDensity] <;>
    apply intervalLaw_eq_base_withDensity <;> linarith

lemma rightLaw_eq_withDensity {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    rightLaw m a b i = baseLaw.withDensity (fun x => ENNReal.ofReal (rightDensity m a b i x)) := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [rightLaw, rightDensity] <;>
    apply intervalLaw_eq_base_withDensity <;> linarith

lemma leftDensity_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) (x : ℝ) :
    0 ≤ leftDensity m a b i x ∧ leftDensity m a b i x ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  constructor
  · fin_cases i <;> exact intervalDensity_nonneg _ _ _
  · fin_cases i <;> simp only [leftDensity, componentVarianceBounds]
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · simpa using intervalDensity_le_inv_length (a := 0) (b := 1 / m)
        (by norm_num) (by linarith) hinv0 x

lemma rightDensity_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) (x : ℝ) :
    0 ≤ rightDensity m a b i x ∧ rightDensity m a b i x ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  constructor
  · fin_cases i <;> exact intervalDensity_nonneg _ _ _
  · fin_cases i <;> simp only [rightDensity, componentVarianceBounds]
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · simpa using intervalDensity_le_inv_length (a := 1 - 1 / m) (b := 1)
        (by linarith) (by norm_num) (by linarith) x

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleDigitGeometry
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace Invariant233.CircleDigitCoupling

lemma bin_subset_unit {r : ℕ} [NeZero r] (d : Fin r) :
    bin r d ⊆ Ico (0 : ℝ) 1 := by
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  intro x hx
  have hd : (d : ℝ) + 1 ≤ r := by exact_mod_cast Nat.succ_le_of_lt d.isLt
  exact ⟨(div_nonneg (by positivity) hr.le).trans hx.1,
    hx.2.trans_le ((div_le_iff₀ hr).mpr (by simpa using hd))⟩

lemma bin_length {r : ℕ} (d : Fin r) :
    ((d : ℝ) + 1) / r - (d : ℝ) / r = 1 / r := by ring

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleDigitCoupling
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

lemma baseLaw_bin {r : ℕ} [NeZero r] (d : Fin r) :
    baseLaw (bin r d) = (r : ℝ≥0∞)⁻¹ := by
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  rw [baseLaw_eq_restrict, Measure.restrict_apply (show MeasurableSet (bin r d) from measurableSet_Ico),
    inter_eq_left.mpr (bin_subset_unit d)]
  rw [bin, Real.volume_Ico, bin_length]
  rw [ENNReal.ofReal_div_of_pos hr]
  simp

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleDigitDensity
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

variable {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)

include hm ha ha' hb hb' in
lemma endpointLaw_eq_density (side : Bool) (l : Label) :
    endpointLaw side m a b l = baseLaw.withDensity
      (fun x => ENNReal.ofReal (endpointDensity side m a b l x)) := by
  have hm0 : 0 < m := by linarith
  cases l with
  | none => simp [endpointLaw, endpointDensity]
  | some i =>
    cases side
    · exact leftLaw_eq_withDensity (by linarith : 2 ≤ 2 * m)
        (width_pos hm0 ha) ha' (width_pos hm0 hb) hb' i
    · exact rightLaw_eq_withDensity (by linarith : 2 ≤ 2 * m)
        (width_pos hm0 ha) ha' (width_pos hm0 hb) hb' i

lemma endpointDensity_measurable (side : Bool) (m a b : ℝ) (l : Label) :
    Measurable (endpointDensity side m a b l) := by
  cases l with
  | none => exact measurable_const
  | some i => cases side <;> fin_cases i <;> exact intervalDensity_measurable _ _

lemma endpointDensity_nonneg (side : Bool) (m a b : ℝ) (l : Label) (x : ℝ) :
    0 ≤ endpointDensity side m a b l x := by
  cases l with
  | none => norm_num [endpointDensity]
  | some i => cases side <;> fin_cases i <;> exact intervalDensity_nonneg _ _ _

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma marginalDensity_bounds (side : Bool) (x : ℝ) :
    49 / 50 ≤ marginalDensity side κ m a b t x ∧
      marginalDensity side κ m a b t x ≤ 3 + 8 * κ ∧
      marginalDensity side κ m a b t x < 10 := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hd (i : Fin 5) : 0 ≤ endpointDensity side m a b (some i) x ∧
      endpointDensity side m a b (some i) x ≤ componentVarianceBounds (2 * m) a b i := by
    cases side
    · exact leftDensity_bound (by linarith) ha0 ha' hb0 hb' i x
    · exact rightDensity_bound (by linarith) ha0 ha' hb0 hb' i x
  have hρa := rho_div_width_le hκ0 hm0 ha
  have hρb := rho_div_width_le hκ0 hm0 hb
  have hρa0 := rho_nonneg (m := m) (w := a) hκ0
  have hρb0 := rho_nonneg (m := m) (w := b) hκ0
  have hq := diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht
  have htag0 : 0 ≤ t / m := div_nonneg ht0 hm0.le
  have htag : (t / m) * endpointDensity side m a b (some 4) x ≤ 2 := by
    calc
      _ ≤ (t / m) * (2 * m) := mul_le_mul_of_nonneg_left (hd 4).2 htag0
      _ = 2 * t := by field_simp
      _ ≤ 2 := by linarith
  have hw (w : ℝ) (v : ℝ) (hw0 : 0 < w) (hρ : rho κ m w / w ≤ κ)
      (hv : v ≤ 2 / w) : rho κ m w * v ≤ 2 * κ := by
    calc
      _ ≤ rho κ m w * (2 / w) := mul_le_mul_of_nonneg_left hv (rho_nonneg hκ0)
      _ = 2 * (rho κ m w / w) := by ring
      _ ≤ _ := by linarith
  have h0 := hw a _ ha0 hρa (hd 0).2
  have h1 := hw a _ ha0 hρa (hd 1).2
  have h2 := hw b _ hb0 hρb (hd 2).2
  have h3 := hw b _ hb0 hρb (hd 3).2
  have hp0 (i : Fin 5) : 0 ≤ componentProbabilities κ m a b t i *
      endpointDensity side m a b (some i) x :=
    mul_nonneg (componentProbabilities_nonneg hκ0 hm0 ht0 i) (hd i).1
  have hlo : 49 / 50 ≤ marginalDensity side κ m a b t x := by
    exact hq.1.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hp0 i)))
  have hup : marginalDensity side κ m a b t x ≤ 3 + 8 * κ := by
    unfold marginalDensity
    simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    change diagonalMass κ m a b t + (rho κ m a * endpointDensity side m a b (some 0) x +
      (rho κ m a * endpointDensity side m a b (some 1) x +
      (rho κ m b * endpointDensity side m a b (some 2) x +
      (rho κ m b * endpointDensity side m a b (some 3) x +
      t / m * endpointDensity side m a b (some 4) x)))) ≤ _
    linarith [hq.2]
  exact ⟨hlo, hup, by linarith⟩

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma ofReal_marginalDensity (side : Bool) (x : ℝ) :
    ENNReal.ofReal (marginalDensity side κ m a b t x) =
      labelMass κ m a b t none + ∑ i : Fin 5,
        labelMass κ m a b t (some i) *
          ENNReal.ofReal (endpointDensity side m a b (some i) x) := by
  have hm0 : 0 < m := by linarith
  apply ofReal_mixture_density
  · exact le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  · exact componentProbabilities_nonneg hκ0 hm0 ht0
  · intro i y
    exact endpointDensity_nonneg side m a b (some i) y

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma digitWeight_total_eq_integral (side : Bool) (r : ℕ) (d : Fin r) :
    (∑ l, digitWeight side r κ m a b t l d) =
      ∫⁻ x in bin r d, ENNReal.ofReal (marginalDensity side κ m a b t x) ∂baseLaw := by
  have h := withDensity_finite_mixture baseLaw (labelMass κ m a b t none)
    (fun i : Fin 5 => labelMass κ m a b t (some i))
    (fun i x => ENNReal.ofReal (endpointDensity side m a b (some i) x))
    (fun i => (endpointDensity_measurable side m a b (some i)).ennreal_ofReal)
  simp_rw [← ofReal_marginalDensity hκ0 hκ hm ha ha' hb hb' ht0 ht side] at h
  have heval := congrArg (fun ν : Measure ℝ => ν (bin r d)) h
  rw [withDensity_apply _ (show MeasurableSet (bin r d) from measurableSet_Ico)] at heval
  rw [heval, Fintype.sum_option]
  simp only [Measure.add_apply, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← endpointLaw_eq_density hm ha ha' hb hb' side (some i)]
  rfl

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma digitWeight_total_le_ten (side : Bool) (r : ℕ) (d : Fin r) :
    (∑ l, digitWeight side r κ m a b t l d) ≤ 10 * baseLaw (bin r d) := by
  rw [digitWeight_total_eq_integral hκ0 hκ hm ha ha' hb hb' ht0 ht]
  calc
    _ ≤ ∫⁻ _x in bin r d, (10 : ℝ≥0∞) ∂baseLaw := by
      apply lintegral_mono
      intro x
      exact le_trans (ENNReal.ofReal_le_ofReal
        (marginalDensity_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht side x).2.2.le)
        (by norm_num)
    _ = _ := by simp

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleDigitDisintegration
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

private lemma map_label_observe {D : Type*} [MeasurableSpace D]
    (ν : Measure (ℝ × ℝ)) [SFinite ν] (l : Label) (f : ℝ × ℝ → D) (hf : Measurable f) :
    (ν.map (fun z => (l, z))).map (fun z : CoordinateSample => (f z.2, z.1)) =
      (ν.map f).prod (Measure.dirac l) := by
  have hin : Measurable (fun z : ℝ × ℝ => (l, z)) := by fun_prop
  have hout : Measurable (fun z : CoordinateSample => (f z.2, z.1)) := by fun_prop
  rw [Measure.map_map hout hin, Measure.prod_dirac]
  rw [Measure.map_map (show Measurable (fun x : D => (x, l)) from by fun_prop) hf]
  rfl

private lemma observed_pair_left {D : Type*} [MeasurableSpace D]
    (ν η : Measure ℝ) [SFinite ν] [IsProbabilityMeasure η]
    (Q : ℝ → D) (hQ : Measurable Q) :
    (ν.prod η).map (fun z => Q z.1) = ν.map Q := by
  change (ν.prod η).map (Q ∘ Prod.fst) = _
  rw [← Measure.map_map hQ measurable_fst, Measure.map_fst_prod]
  simp

private lemma observed_pair_right {D : Type*} [MeasurableSpace D]
    (ν η : Measure ℝ) [IsProbabilityMeasure ν] [SFinite η]
    (Q : ℝ → D) (hQ : Measurable Q) :
    (ν.prod η).map (fun z => Q z.2) = η.map Q := by
  change (ν.prod η).map (Q ∘ Prod.snd) = _
  rw [← Measure.map_map hQ measurable_snd, Measure.map_snd_prod]
  simp

variable {κ m a b t : ℝ}
    (hm : 100 ≤ m) (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
include hm ha ha' hb hb'

lemma endpointLaw_ae_unit (side : Bool) (l : Label) :
    ∀ᵐ x ∂endpointLaw side m a b l, x ∈ Ico (0 : ℝ) 1 := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hinv : 1 / (2 * m) ≤ 1 := by apply (div_le_iff₀ (by linarith : 0 < 2 * m)).2; linarith
  have hinv0 : 0 < 1 / (2 * m) := one_div_pos.mpr (by linarith)
  cases l with
  | none => exact intervalLaw_ae_mem 0 1
  | some i =>
    cases side <;> fin_cases i <;> simp only [endpointLaw, Bool.false_eq_true, ite_false, if_false,
      ite_true, if_true, leftLaw, rightLaw]
    all_goals
      filter_upwards [intervalLaw_ae_mem _ _] with x hx
      constructor <;> linarith [hx.1, hx.2]

lemma endpointLaw_quantize_singleton (side : Bool) (r : ℕ) [NeZero r]
    (l : Label) (d : Fin r) :
    (endpointLaw side m a b l).map (UniformQuantization.quantize r) {d} =
      endpointLaw side m a b l (bin r d) := by
  rw [Measure.map_apply (UniformQuantization.measurable_quantize r) (measurableSet_singleton d)]
  apply measure_congr
  filter_upwards [endpointLaw_ae_unit hm ha ha' hb hb' side l] with x hx
  exact propext (UniformQuantization.quantize_eq_iff d hx)

lemma digitJoint_eq_sum (side : Bool) (r : ℕ) [NeZero r] :
    digitJoint side r κ m a b t =
      ∑ l, labelMass κ m a b t l •
        ((endpointLaw side m a b l).map (UniformQuantization.quantize r)).prod (Measure.dirac l) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have hQ := UniformQuantization.measurable_quantize r
  have hmap : Measurable (fun z : CoordinateSample =>
      (UniformQuantization.quantize r (endpoint side z), z.1)) := by
    cases side <;> dsimp [endpoint] <;> fun_prop
  unfold digitJoint rawLaw labelledMixture
  rw [Measure.map_add _ _ hmap, map_finsetSum _ _ hmap, Fintype.sum_option]
  simp only [Measure.map_smul]
  congr 1
  · cases side <;> simp only [endpoint, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
      labelMass, endpointLaw]
    all_goals
      first
      | rw [map_label_observe _ _ (fun z : ℝ × ℝ => UniformQuantization.quantize r z.1) (by fun_prop)]
      | rw [map_label_observe _ _ (fun z : ℝ × ℝ => UniformQuantization.quantize r z.2) (by fun_prop)]
      congr 2
      unfold CouplingMixture.diagonal
      have hdiag : Measurable (fun x : ℝ => (x, x)) := by fun_prop
      have hleft : Measurable (fun z : ℝ × ℝ => UniformQuantization.quantize r z.1) := by fun_prop
      have hright : Measurable (fun z : ℝ × ℝ => UniformQuantization.quantize r z.2) := by fun_prop
      first
      | rw [Measure.map_map hleft hdiag]
      | rw [Measure.map_map hright hdiag]
      rfl
  · apply Finset.sum_congr rfl
    intro i _
    cases side <;> simp only [endpoint, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
      labelMass, endpointLaw]
    · rw [map_label_observe _ _ (fun z : ℝ × ℝ => UniformQuantization.quantize r z.1) (by fun_prop), observed_pair_left _ _ _ hQ]
    · rw [map_label_observe _ _ (fun z : ℝ × ℝ => UniformQuantization.quantize r z.2) (by fun_prop), observed_pair_right _ _ _ hQ]

lemma digitJoint_fst_singleton (side : Bool) (r : ℕ) [NeZero r] (d : Fin r) :
    (digitJoint side r κ m a b t).fst {d} =
      ∑ l, digitWeight side r κ m a b t l d := by
  rw [digitJoint_eq_sum hm ha ha' hb hb', Measure.fst,
    map_finsetSum _ _ measurable_fst]
  simp only [Measure.map_smul, Measure.map_fst_prod,
    measure_univ, one_smul,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [endpointLaw_quantize_singleton hm ha ha' hb hb']
  rfl

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixNonterminal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Invariant233

theorem infinitePi_eventually_mem_null
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (s : (n : ℕ) → Set (X n)) (hs : ∀ n, MeasurableSet (s n))
    {q : ℝ≥0∞} (hq : q < 1) (hprob : ∀ n, μ n (s n) ≤ q) :
    (Measure.infinitePi μ) {x | ∃ N : ℕ, ∀ n, N ≤ n → x n ∈ s n} = 0 := by
  have htail (N k : ℕ) :
      (Measure.infinitePi μ) {x | ∀ n, N ≤ n → x n ∈ s n} ≤ q ^ k := by
    calc
      (Measure.infinitePi μ) {x | ∀ n, N ≤ n → x n ∈ s n} ≤
          (Measure.infinitePi μ) (Set.pi (Finset.Ico N (N + k)) s) := by
        apply measure_mono
        intro x hx n hn
        exact hx n (Finset.mem_Ico.mp hn).1
      _ = ∏ n ∈ Finset.Ico N (N + k), μ n (s n) :=
        Measure.infinitePi_pi μ (fun n _ => hs n)
      _ ≤ ∏ _n ∈ Finset.Ico N (N + k), q :=
        Finset.prod_le_prod' (fun n _ => hprob n)
      _ = q ^ k := by simp
  have hnull (N : ℕ) :
      (Measure.infinitePi μ) {x | ∀ n, N ≤ n → x n ∈ s n} = 0 := by
    apply le_antisymm _ bot_le
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
      (Eventually.of_forall (htail N))
  have heq : {x : (n : ℕ) → X n | ∃ N : ℕ, ∀ n, N ≤ n → x n ∈ s n} =
      ⋃ N : ℕ, {x | ∀ n, N ≤ n → x n ∈ s n} := by
    ext x
    simp
  rw [heq]
  exact measure_iUnion_null hnull

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingNonterminal
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

lemma initial_digit_singleton {p : CircleParameterData}
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ)
    (d : Fin (MixedRadix.radices p.q i)) :
    (initialLaw.map (observedDigit p hr side i)) {d} =
      (MixedRadix.radices p.q i : ℝ≥0∞)⁻¹ := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  rw [initialLaw, Measure.map_map (measurable_observedDigit hr side i)
    (show Measurable (fun x : ℝ => ((none : Label), (x, x))) from by fun_prop)]
  cases side <;>
    change (baseLaw.map (UniformQuantization.quantize _)) {d} = _
  all_goals rw [baseLaw_eq_restrict]; exact UniformQuantization.map_quantize_singleton _ d

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma observed_singleton_le_half (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ)
    (d : Fin (MixedRadix.radices p.q i)) :
    ((coordinateLaw p j i).map (observedDigit p hr side i)) {d} ≤ (2 : ℝ≥0∞)⁻¹ := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  by_cases hi : i = 0
  · rw [coordinateLaw, ite_eq_left hi, initial_digit_singleton]
    exact ENNReal.inv_le_inv.mpr (by exact_mod_cast
      (MixedRadix.radices_ge_two hp.q_pos hp.frequency_increasing hp.frequency_divisible i))
  obtain ⟨s, hs, his⟩ := p.exists_mem_block hp.m_pos i (by omega)
  have hidx := p.blockIndex_eq_of_mem hp.m_pos his
  have hm : (100 : ℝ) ≤ p.m s := by exact_mod_cast (show 100 ≤ p.m s by have := hp.m_ge_200 s hs; omega)
  have ha := hp.coupling_a_bounds s hs
  have hb := hp.coupling_b_bounds s hs
  have hκ := CircleParameterLaws.coupling_kappa_bounds s hs
  have ht := tag_bounds j s
  have h20 : (20 : ℝ) ≤ MixedRadix.radices p.q i := by
    have hN := hp.coupling_radix_ge_N hs his
    have hK : (100 : ℝ) ≤ p.K s := by exact_mod_cast hp.coupling_K_ge s hs
    dsimp [N] at hN
    nlinarith
  rw [coordinateLaw, ite_eq_right hi, hidx]
  have hfst := Measure.fst_map_prodMk (μ := rawLaw (kappa s) (p.m s) (p.a s) (p.b s) (tag j s))
    (X := observedDigit p hr side i) measurable_fst
  rw [← hfst]
  change (digitJoint side (MixedRadix.radices p.q i) (kappa s) (p.m s) (p.a s) (p.b s) (tag j s)).fst {d} ≤ _
  rw [digitJoint_fst_singleton hm ha.1 ha.2 hb.1 hb.2]
  calc
    _ ≤ 10 * baseLaw (bin _ d) := digitWeight_total_le_ten hκ.1 hκ.2 hm ha.1 ha.2 hb.1 hb.2 ht.1 ht.2 side _ d
    _ = 10 * (MixedRadix.radices p.q i : ℝ≥0∞)⁻¹ := by rw [baseLaw_bin]
    _ ≤ 10 * (20 : ℝ≥0∞)⁻¹ := mul_le_mul_right (ENNReal.inv_le_inv.mpr (by exact_mod_cast h20)) 10
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num

lemma ae_nonterminal_digits (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    ∀ᵐ ω ∂law p j, MixedRadix.Nonterminal (digits p hr side ω) := by
  let := coordinateLaw_isProbabilityMeasure hp j
  let s : ℕ → Set CoordinateSample := fun i =>
    {z | ¬(observedDigit p hr side i z : ℕ) + 1 < MixedRadix.radices p.q i}
  have heq (i : ℕ) : s i = observedDigit p hr side i ⁻¹'
      {⟨MixedRadix.radices p.q i - 1, by have := hr i; omega⟩} := by
    ext z
    simp only [s, mem_ofPred_eq, mem_preimage, mem_singleton_iff, Fin.ext_iff]
    have := (observedDigit p hr side i z).isLt
    omega
  have hs (i : ℕ) : MeasurableSet (s i) := by
    rw [heq]
    exact (measurable_observedDigit hr side i) (measurableSet_singleton _)
  have hprob (i : ℕ) : coordinateLaw p j i (s i) ≤ (2 : ℝ≥0∞)⁻¹ := by
    rw [heq, ← Measure.map_apply (measurable_observedDigit hr side i) (measurableSet_singleton _)]
    exact observed_singleton_le_half hp j hr side i _
  have hnull := infinitePi_eventually_mem_null (coordinateLaw p j) s hs
    (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1) hprob
  rw [ae_iff]
  simpa only [law, MixedRadix.Nonterminal, digits, mem_ofPred_eq,
    not_forall, not_exists, not_and, s] using hnull

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingCrossings
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma coordinate_point_eq_tail (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (side : Bool) (ω : Sample) (hnt : MixedRadix.Nonterminal (digits p hr side ω)) (i : ℕ) :
    p.coordinate i (point p hr side ω) = MixedRadix.tailValue (digits p hr side ω) i := by
  unfold coordinate point MixedRadix.circleValue
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  change CircleParameterData.rep (((p.q i : ℝ) * MixedRadix.ofDigits (digits p hr side ω) : ℝ) : Circle) = _
  rw [show CircleParameterData.rep = (fun x : Circle => (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)) from rfl,
    CircleCharacterDynamics.representative_coe]
  exact MixedRadix.coordinate_eq_tailValue hp.frequency_zero hp.q_pos
    hp.frequency_increasing hp.frequency_divisible _ hnt i

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingSupport
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMixture CouplingMarginalBounds OneCoordinateCoupling

lemma rawLaw_ae_of_components {κ m a b t : ℝ} {P : CoordinateSample → Prop}
    (hP : MeasurableSet {z | P z})
    (hdiag : ∀ᵐ x ∂baseLaw, P (none, (x, x)))
    (hcomp : ∀ i : Fin 5, ∀ᵐ z ∂(leftLaw (2 * m) a b i).prod (rightLaw (2 * m) a b i),
      P (some i, z)) : ∀ᵐ z ∂rawLaw κ m a b t, P z := by
  unfold rawLaw labelledMixture
  rw [ae_add_measure_iff, ae_finsetSum_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (show Measurable (fun z : ℝ × ℝ => ((none : Label), z)) from by fun_prop).aemeasurable hP).2
    unfold CouplingMixture.diagonal
    exact (ae_map_iff (show Measurable (fun x : ℝ => (x, x)) from by fun_prop).aemeasurable
      (show MeasurableSet {z : ℝ × ℝ | P (none, z)} from
        (show Measurable (fun z : ℝ × ℝ => ((none : Label), z)) from by fun_prop) hP)).2 hdiag
  · intro i _
    exact Measure.ae_smul_measure
      ((ae_map_iff (show Measurable (fun z : ℝ × ℝ => (some i, z)) from by fun_prop).aemeasurable hP).2 (hcomp i)) _

section Parameters
variable {κ m a b t : ℝ}
    (hm : 100 ≤ m) (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
include hm ha ha' hb hb'

lemma rawLaw_ae_endpoint_property (side : Bool) {P : Label → ℝ → Prop}
    (hP : MeasurableSet {z : CoordinateSample | P z.1 (endpoint side z)})
    (hbase : ∀ᵐ x ∂baseLaw, P none x)
    (hl : ∀ i : Fin 5, ∀ᵐ x ∂endpointLaw side m a b (some i), P (some i) x) :
    ∀ᵐ z ∂rawLaw κ m a b t, P z.1 (endpoint side z) := by
  have hm0 : 0 < m := by linarith
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) (width_pos hm0 ha) ha' (width_pos hm0 hb) hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) (width_pos hm0 ha) ha' (width_pos hm0 hb) hb'
  apply rawLaw_ae_of_components hP
  · cases side <;> exact hbase
  · intro i
    cases side
    · exact (measurePreserving_fst (μ := leftLaw (2 * m) a b i)
        (ν := rightLaw (2 * m) a b i)).quasiMeasurePreserving.ae (hl i)
    · exact (measurePreserving_snd (μ := leftLaw (2 * m) a b i)
        (ν := rightLaw (2 * m) a b i)).quasiMeasurePreserving.ae (hl i)

lemma rawLaw_ae_endpoint_unit (side : Bool) :
    ∀ᵐ z ∂rawLaw κ m a b t, endpoint side z ∈ Ico (0 : ℝ) 1 := by
  apply rawLaw_ae_endpoint_property hm ha ha' hb hb' side (P := fun _ x => x ∈ Ico (0 : ℝ) 1)
  · apply measurableSet_Ico.preimage
    cases side
    · exact measurable_fst.comp measurable_snd
    · exact measurable_snd.comp measurable_snd
  · exact intervalLaw_ae_mem 0 1
  · intro i
    exact endpointLaw_ae_unit hm ha ha' hb hb' side (some i)

end Parameters
end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingOrder
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Invariant233.UniformQuantization

lemma quantize_mono_on_unit {q : ℕ} [NeZero q] {x y : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) (hy : y ∈ Ico (0 : ℝ) 1) (hxy : x ≤ y) :
    quantize q x ≤ quantize q y := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hfx : ⌊(q : ℝ) * x⌋₊ < q :=
    (Nat.floor_lt (mul_nonneg hq.le hx.1)).mpr (by nlinarith [hx.2])
  have hfy : ⌊(q : ℝ) * y⌋₊ < q :=
    (Nat.floor_lt (mul_nonneg hq.le hy.1)).mpr (by nlinarith [hy.2])
  change ⌊(q : ℝ) * x⌋₊ % q ≤ ⌊(q : ℝ) * y⌋₊ % q
  rw [Nat.mod_eq_of_lt hfx, Nat.mod_eq_of_lt hfy]
  exact Nat.floor_mono (mul_le_mul_of_nonneg_left hxy hq.le)

end Invariant233.UniformQuantization

namespace Invariant233.CircleDigitCoupling
open OneCoordinateCoupling

lemma rawLaw_ae_ordered {κ m a b t : ℝ} (hm : 1 ≤ m) :
    ∀ᵐ z ∂rawLaw κ m a b t, endpoint false z ≤ endpoint true z := by
  apply rawLaw_ae_of_components
  · exact measurableSet_le (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd)
  · exact Eventually.of_forall (fun _ => le_rfl)
  · exact replacement_ae_ordered (by linarith : 2 ≤ 2 * m)

end Invariant233.CircleDigitCoupling

namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma coordinateLaw_ae_ordered (j i : ℕ) :
    ∀ᵐ z ∂coordinateLaw p j i, endpoint false z ≤ endpoint true z := by
  by_cases hi : i = 0
  · rw [coordinateLaw, ite_eq_left hi, initialLaw]
    apply (ae_map_iff (show Measurable (fun x : ℝ => ((none : Label), (x, x))) from by fun_prop).aemeasurable
      (measurableSet_le (measurable_fst.comp measurable_snd)
        (measurable_snd.comp measurable_snd))).2
    exact Eventually.of_forall (fun _ => le_rfl)
  · rw [coordinateLaw, ite_eq_right hi]
    apply rawLaw_ae_ordered
    have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
    exact_mod_cast (show 1 ≤ p.m (p.blockIndex i) by
      have := hp.m_ge_200 _ hs
      omega)

lemma coordinateLaw_ae_endpoint_unit (j : ℕ) (side : Bool) (i : ℕ) :
    ∀ᵐ z ∂coordinateLaw p j i, endpoint side z ∈ Ico (0 : ℝ) 1 := by
  by_cases hi : i = 0
  · rw [coordinateLaw, ite_eq_left hi, initialLaw]
    have hmeas : Measurable (endpoint side) := by
      cases side
      · exact measurable_fst.comp measurable_snd
      · exact measurable_snd.comp measurable_snd
    apply (ae_map_iff (show Measurable (fun x : ℝ => ((none : Label), (x, x))) from by fun_prop).aemeasurable
      (measurableSet_Ico.preimage hmeas)).2
    cases side <;> exact CouplingMixture.intervalLaw_ae_mem 0 1
  · rw [coordinateLaw, ite_eq_right hi]
    have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
    have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
      exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by
        have := hp.m_ge_200 _ hs
        omega)
    exact rawLaw_ae_endpoint_unit hm (hp.coupling_a_bounds _ hs).1
      (hp.coupling_a_bounds _ hs).2 (hp.coupling_b_bounds _ hs).1
      (hp.coupling_b_bounds _ hs).2 side

lemma ae_digits_ordered (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    ∀ᵐ ω ∂law p j, ∀ i, digits p hr false ω i ≤ digits p hr true ω i := by
  let := coordinateLaw_isProbabilityMeasure hp j
  apply ae_all_iff.2
  intro i
  have h : ∀ᵐ z ∂coordinateLaw p j i,
      observedDigit p hr false i z ≤ observedDigit p hr true i z := by
    filter_upwards [coordinateLaw_ae_ordered hp j i,
      coordinateLaw_ae_endpoint_unit hp j false i,
      coordinateLaw_ae_endpoint_unit hp j true i] with z hz hx hy
    let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
    exact UniformQuantization.quantize_mono_on_unit hx hy hz
  exact (measurePreserving_eval_infinitePi (coordinateLaw p j) i).quasiMeasurePreserving.ae h

lemma ae_coordinates_ordered (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    ∀ᵐ ω ∂law p j, ∀ i,
      p.coordinate i (point p hr false ω) ≤ p.coordinate i (point p hr true ω) := by
  filter_upwards [ae_digits_ordered hp j hr, ae_nonterminal_digits hp j hr false,
    ae_nonterminal_digits hp j hr true] with ω horder hx hy
  intro i
  rw [coordinate_point_eq_tail hp hr false ω hx i,
    coordinate_point_eq_tail hp hr true ω hy i]
  exact MixedRadix.tailValue_mono hr horder i

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleTailAttenuation
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
namespace Invariant233.CircleCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem actual_tail_attenuation (j : ℕ) (hj : 1 ≤ j)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) : TailAttenuation θ p j hr :=
  actual_tail_attenuation_of_ac_order hp j hj hr
    (endpoint_absolutelyContinuous hp j hr)
    ((ae_coordinates_ordered hp j hr).mono (fun _ h i => h i.2))

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleTailExceptionalFamilies
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
namespace Invariant233.CircleCoupling

theorem tail_exceptional_families_of_subset_oai
    {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
    (j : ℕ) (hj : 1 ≤ j) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (E : Set Sample) (hEm : MeasurableSet E) (hE : E ⊆ tagEvent p j) :
    ∃ H₁ H₂ : ℤ → Set Sample,
      (∀ k, MeasurableSet (H₁ k)) ∧ (∀ k, MeasurableSet (H₂ k)) ∧
      (∀ k : ℤ, (p.K j : ℤ) < |k| → ∀ᵐ ω ∂law p j,
        ((law p j)[(H₁ k).indicator (fun _ => (1 : ℝ)) | endpointSigma p hr false]) ω ≤
          Real.exp (-p.L j / 400)) ∧
      (∀ k : ℤ, (p.K j : ℤ) < |k| → ∀ᵐ ω ∂law p j,
        ((law p j)[(H₂ k).indicator (fun _ => (1 : ℝ)) | endpointSigma p hr true]) ω ≤
          Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂(law p j).restrict E, ∀ k : ℤ, (p.K j : ℤ) < |k| →
        p.floorCocycle θ k (point p hr true ω) /
          p.floorCocycle θ k (point p hr false ω) ≤
          Real.exp (-p.L j) + (H₁ k).indicator (fun _ => (1 : ℝ)) ω +
            (H₂ k).indicator (fun _ => (1 : ℝ)) ω) := by
  classical
  let I := {k : ℤ // (p.K j : ℝ) < |(k : ℝ)|}
  have hex (k : I) := actual_tail_attenuation hp j hj hr k.1 k.2
  choose H₁ H₂ hm₁ hm₂ hc₁ hc₂ hb using hex
  let A₁ : ℤ → Set Sample := fun k =>
    if hk : (p.K j : ℝ) < |(k : ℝ)| then H₁ ⟨k, hk⟩ else ∅
  let A₂ : ℤ → Set Sample := fun k =>
    if hk : (p.K j : ℝ) < |(k : ℝ)| then H₂ ⟨k, hk⟩ else ∅
  have hreal (k : ℤ) (hk : (p.K j : ℤ) < |k|) :
      (p.K j : ℝ) < |(k : ℝ)| := by exact_mod_cast hk
  refine ⟨A₁, A₂, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    dsimp [A₁]
    split_ifs with hk
    · exact hm₁ ⟨k, hk⟩
    · exact MeasurableSet.empty
  · intro k
    dsimp [A₂]
    split_ifs with hk
    · exact hm₂ ⟨k, hk⟩
    · exact MeasurableSet.empty
  · intro k hk
    simpa only [A₁, dite_eq_left (hreal k hk)] using hc₁ ⟨k, hreal k hk⟩
  · intro k hk
    simpa only [A₂, dite_eq_left (hreal k hk)] using hc₂ ⟨k, hreal k hk⟩
  · have hall := ae_all_iff.mpr hb
    filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem hEm] with ω hω hmem
    intro k hk
    simpa only [A₁, A₂, dite_eq_left (hreal k hk)] using
      hω ⟨k, hreal k hk⟩ (hE hmem)

end Invariant233.CircleCoupling

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.CircleCoupling.tail_exceptional_families_of_subset_oai := @OAI.Invariant233.CircleCoupling.tail_exceptional_families_of_subset_oai
