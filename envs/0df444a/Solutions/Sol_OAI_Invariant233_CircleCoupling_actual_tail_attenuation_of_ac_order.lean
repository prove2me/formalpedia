-- Prove2me | solution 1 for OAI.Invariant233.CircleCoupling.actual_tail_attenuation_of_ac_order
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:48.575112+00:00
-- url     : https://prove2.me/submissions/6f4954b0-0af9-4418-b3d9-9d630a9949c0

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Floor.Ring
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
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Condexp
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
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_CrossingAvoidance
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Invariant233.CrossingAvoidance

variable {ι Ω : Type*} [MeasurableSpace Ω]

theorem measureReal_avoid_eq_prod (μ : Measure Ω) [IsProbabilityMeasure μ]
    (events : ι → Set Ω) (hind : iIndepSet events μ)
    (hmeas : ∀ i, MeasurableSet (events i)) (s : Finset ι) :
    μ.real (⋂ i ∈ s, (events i)ᶜ) = ∏ i ∈ s, (1 - μ.real (events i)) := by
  have hprod : μ (⋂ i ∈ s, (events i)ᶜ) = ∏ i ∈ s, μ ((events i)ᶜ) := by
    apply (iIndepSet_iff events μ).mp hind s
    intro i hi
    exact (MeasurableSpace.measurableSet_generateFrom (by simp)).compl
  change (μ (⋂ i ∈ s, (events i)ᶜ)).toReal = _
  rw [hprod, ENNReal.toReal_prod]
  congr 1
  funext i
  change μ.real ((events i)ᶜ) = _
  rw [measureReal_compl (hmeas i), probReal_univ]

theorem measureReal_avoid_le_exp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (events : ι → Set Ω) (hind : iIndepSet events μ)
    (hmeas : ∀ i, MeasurableSet (events i)) (s : Finset ι) (p : ℝ)
    (hp : ∀ i ∈ s, p ≤ μ.real (events i)) :
    μ.real (⋂ i ∈ s, (events i)ᶜ) ≤ Real.exp (-(s.card : ℝ) * p) := by
  rw [measureReal_avoid_eq_prod μ events hind hmeas s]
  calc
    ∏ i ∈ s, (1 - μ.real (events i)) ≤ ∏ _i ∈ s, Real.exp (-p) := by
      apply Finset.prod_le_prod
      · intro i hi
        rw [← probReal_univ (μ := μ)]
        exact sub_nonneg.mpr (measureReal_mono (Set.subset_univ _))
      · intro i hi
        exact (sub_le_sub_left (hp i hi) 1).trans (Real.one_sub_le_exp_neg p)
    _ = Real.exp (-(s.card : ℝ) * p) := by
      rw [← Real.exp_sum]
      congr 1
      simp

theorem measureReal_le_exp_of_subset_avoid (μ : Measure Ω) [IsProbabilityMeasure μ]
    (events : ι → Set Ω) (hind : iIndepSet events μ)
    (hmeas : ∀ i, MeasurableSet (events i)) (s : Finset ι) (p : ℝ)
    (hp : ∀ i ∈ s, p ≤ μ.real (events i)) (bad : Set Ω)
    (hbad : bad ⊆ ⋂ i ∈ s, (events i)ᶜ) :
    μ.real bad ≤ Real.exp (-(s.card : ℝ) * p) :=
  (measureReal_mono hbad).trans (measureReal_avoid_le_exp μ events hind hmeas s p hp)

theorem exp_card_bound (s : Finset ι) (m ρ : ℝ) (hρ : 0 ≤ ρ)
    (hcard : m / 40 ≤ (s.card : ℝ)) :
    Real.exp (-(s.card : ℝ) * (ρ / 10)) ≤ Real.exp (-m * ρ / 400) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hcard hρ
  nlinarith

theorem measureReal_le_exp_four_hundred (μ : Measure Ω) [IsProbabilityMeasure μ]
    (events : ι → Set Ω) (hind : iIndepSet events μ)
    (hmeas : ∀ i, MeasurableSet (events i)) (s : Finset ι) (m ρ : ℝ)
    (hρ : 0 ≤ ρ) (hcard : m / 40 ≤ (s.card : ℝ))
    (hp : ∀ i ∈ s, ρ / 10 ≤ μ.real (events i)) (bad : Set Ω)
    (hbad : bad ⊆ ⋂ i ∈ s, (events i)ᶜ) :
    μ.real bad ≤ Real.exp (-m * ρ / 400) :=
  (measureReal_le_exp_of_subset_avoid μ events hind hmeas s (ρ / 10) hp bad hbad).trans
    (exp_card_bound s m ρ hρ hcard)

theorem measureReal_le_exp_intensity (μ : Measure Ω) [IsProbabilityMeasure μ]
    (events : ι → Set Ω) (hind : iIndepSet events μ)
    (hmeas : ∀ i, MeasurableSet (events i)) (s : Finset ι) (m ρ L : ℝ)
    (hρ : 0 ≤ ρ) (hcard : m / 40 ≤ (s.card : ℝ)) (hL : L ≤ m * ρ)
    (hp : ∀ i ∈ s, ρ / 10 ≤ μ.real (events i)) (bad : Set Ω)
    (hbad : bad ⊆ ⋂ i ∈ s, (events i)ᶜ) :
    μ.real bad ≤ Real.exp (-L / 400) := by
  refine (measureReal_le_exp_four_hundred μ events hind hmeas s m ρ hρ hcard hp bad hbad).trans ?_
  apply Real.exp_le_exp.mpr
  linarith


variable {α : Type*} [LinearOrder α] (s : Finset ι) (x y u : ι → α)

theorem below_iff_of_no_crossing
    (horder : ∀ i ∈ s, x i ≤ y i)
    (hno : ∀ i ∈ s, ¬ (x i < u i ∧ u i ≤ y i)) :
    ∀ i ∈ s, x i < u i ↔ y i < u i := by
  intro i hi
  constructor
  · intro hxu
    exact lt_of_not_ge (fun huy => hno i hi ⟨hxu, huy⟩)
  · intro hyu
    exact lt_of_le_of_lt (horder i hi) hyu

theorem below_card_add_above_card
    (horder : ∀ i ∈ s, x i ≤ y i)
    (hno : ∀ i ∈ s, ¬ (x i < u i ∧ u i ≤ y i)) :
    (s.filter (fun i => x i < u i)).card +
      (s.filter (fun i => u i ≤ y i)).card = s.card := by
  classical
  have heq : s.filter (fun i => u i ≤ y i) = s.filter (fun i => ¬ x i < u i) := by
    apply Finset.filter_congr
    intro i hi
    rw [below_iff_of_no_crossing s x y u horder hno i hi, not_lt]
  rw [heq]
  exact Finset.card_filter_add_card_filter_not _

theorem above_half_of_below_not_half
    (horder : ∀ i ∈ s, x i ≤ y i)
    (hno : ∀ i ∈ s, ¬ (x i < u i ∧ u i ≤ y i))
    (hsmall : ¬ s.card ≤ 2 * (s.filter (fun i => x i < u i)).card) :
    s.card ≤ 2 * (s.filter (fun i => u i ≤ y i)).card := by
  classical
  have hsum := below_card_add_above_card s x y u horder hno
  omega

theorem eligible_card_lower_bound (eligible : Finset ι) (m : ℝ)
    (hcandidates : m / 20 ≤ (s.card : ℝ))
    (heligible : s.card ≤ 2 * eligible.card) :
    m / 40 ≤ (eligible.card : ℝ) := by
  have hcast : (s.card : ℝ) ≤ 2 * (eligible.card : ℝ) := by exact_mod_cast heligible
  linarith


end Invariant233.CrossingAvoidance

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FiniteKernelMixture
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace Invariant233.FiniteKernelMixture

variable {I X Y : Type*} [Fintype I] [MeasurableSpace X] [MeasurableSpace Y]

theorem normalizedKernel_isMarkov (κ : I → Kernel X Y) [∀ i, IsMarkovKernel (κ i)]
    (w : I → X → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (h0 : ∀ x, (∑ i, w i x) ≠ 0) (ht : ∀ x, (∑ i, w i x) ≠ ∞) :
    IsMarkovKernel (normalizedKernel κ w hw) := by
  constructor
  intro x
  constructor
  simp only [normalizedKernel_apply, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact ENNReal.mul_inv_cancel (h0 x) (ht x)

end Invariant233.FiniteKernelMixture

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TailScaleCover
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233
namespace TailScaleCover

theorem exists_window_of_overlap (left right : ℕ → ℝ) (j : ℕ) (t : ℝ)
    (hunbounded : ∀ R : ℝ, ∃ s : ℕ, j ≤ s ∧ R ≤ right s)
    (hoverlap : ∀ s : ℕ, j ≤ s → left (s + 1) ≤ right s) :
    ∃ s : ℕ, j ≤ s ∧ t ≤ right s ∧ (s = j ∨ left s ≤ t) := by
  have hex : ∃ n : ℕ, t ≤ right (j + n) := by
    obtain ⟨s, hjs, hs⟩ := hunbounded t
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjs
    exact ⟨n, hs⟩
  let n := Nat.find hex
  have hn : t ≤ right (j + n) := Nat.find_spec hex
  refine ⟨j + n, by omega, hn, ?_⟩
  by_cases hn0 : n = 0
  · left
    simp [hn0]
  · right
    have hprev : ¬ t ≤ right (j + (n - 1)) :=
      Nat.find_min hex (show n - 1 < Nat.find hex by change n - 1 < n; omega)
    have hstep := hoverlap (j + (n - 1)) (by omega)
    have heq : j + (n - 1) + 1 = j + n := by omega
    rw [heq] at hstep
    exact hstep.trans (le_of_lt (lt_of_not_ge hprev))

theorem lower_intensity_eq (κ G m : ℝ) (hG : 0 ≤ G) (hm : 0 < m) :
    m * (κ * Real.sqrt ((G / m) / m)) = κ * Real.sqrt G := by
  have hdiv : (G / m) / m = G / m ^ 2 := by ring
  rw [hdiv, Real.sqrt_div hG, Real.sqrt_sq hm.le]
  field_simp

theorem upper_intensity_eq (κ m : ℝ) (hm : 0 < m) :
    m * (κ * Real.sqrt (m ^ (-(19 / 20 : ℝ)) / m)) =
      κ * m ^ (1 / 40 : ℝ) := by
  have hdiv : m ^ (-(19 / 20 : ℝ)) / m = m ^ (-(39 / 20 : ℝ)) := by
    calc
      _ = m ^ (-(19 / 20 : ℝ)) / m ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = m ^ (-(19 / 20 : ℝ) - 1) := (Real.rpow_sub hm _ _).symm
      _ = _ := by norm_num
  have hsqrt : Real.sqrt (m ^ (-(19 / 20 : ℝ)) / m) =
      m ^ (-(39 / 40 : ℝ)) := by
    rw [hdiv, Real.sqrt_eq_rpow, ← Real.rpow_mul hm.le]
    norm_num
  rw [hsqrt]
  calc
    _ = κ * (m ^ (1 : ℝ) * m ^ (-(39 / 40 : ℝ))) := by
      rw [Real.rpow_one]
      ring
    _ = κ * m ^ ((1 : ℝ) + -(39 / 40 : ℝ)) := by rw [Real.rpow_add hm]
    _ = _ := by norm_num

end TailScaleCover

namespace CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem index_le_tail_horizon (s : ℕ) (hs : 1 ≤ s) :
    (s : ℝ) ≤ (p.m s : ℝ) ^ ((4 / 5 : ℝ) * p.m s) := by
  have hsm : s ≤ p.m s := (Nat.lt_two_pow_self.le).trans (hp.m_ge_pow s hs)
  have hm200 : (200 : ℝ) ≤ p.m s := by exact_mod_cast hp.m_ge_200 s hs
  calc
    (s : ℝ) ≤ (p.m s : ℝ) := by exact_mod_cast hsm
    _ = (p.m s : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem tail_windows_cover (j : ℕ) (hj : 1 ≤ j) (t : ℝ)
    (ht : p.N j / 4 ≤ t) :
    ∃ s : ℕ, j ≤ s ∧ t ≤ (p.m s : ℝ) ^ ((4 / 5 : ℝ) * p.m s) ∧
      ((s = j ∧ p.N s / 4 ≤ t) ∨ (j < s ∧ (p.G s : ℝ) * p.K s ≤ t)) := by
  obtain ⟨s, hjs, hs, hleft⟩ := TailScaleCover.exists_window_of_overlap
    (fun s => (p.G s : ℝ) * p.K s)
    (fun s => (p.m s : ℝ) ^ ((4 / 5 : ℝ) * p.m s)) j t
    (by
      intro R
      obtain ⟨n, hn⟩ := exists_nat_gt (max R (j : ℝ))
      have hjn : j ≤ n := by
        have hlt : (j : ℝ) < n := (le_max_right _ _).trans_lt hn
        exact_mod_cast hlt.le
      refine ⟨n, hjn, ?_⟩
      exact ((le_max_left _ _).trans hn.le).trans
        (hp.index_le_tail_horizon n (hj.trans hjn)))
    (fun s hs => (hp.next_G_gap s (hj.trans hs)).le)
  refine ⟨s, hjs, hs, ?_⟩
  rcases hleft with hsj | hleft
  · left
    exact ⟨hsj, hsj ▸ ht⟩
  · by_cases hsj : s = j
    · left
      exact ⟨hsj, hsj ▸ ht⟩
    · right
      exact ⟨lt_of_le_of_ne hjs (Ne.symm hsj), hleft⟩

theorem upper_crossing_intensity (j s : ℕ) (hj : 1 ≤ j) (hjs : j ≤ s) :
    p.L j ≤ (p.m s : ℝ) *
      (kappa s * Real.sqrt (p.b s / (p.m s : ℝ))) := by
  have hs := hj.trans hjs
  have hm : 0 < (p.m s : ℝ) := by exact_mod_cast hp.m_pos s hs
  rw [CircleParameterData.b, TailScaleCover.upper_intensity_eq _ _ hm]
  exact (hp.L_monotone j s hj hjs).trans (hp.attenuation_m s hs)

theorem lower_crossing_intensity (j s : ℕ) (hj : 1 ≤ j) (hjs : j < s) :
    p.L j ≤ (p.m s : ℝ) *
      (kappa s * Real.sqrt (p.a s / (p.m s : ℝ))) := by
  have hs : 1 ≤ s := by omega
  have hm : 0 < (p.m s : ℝ) := by exact_mod_cast hp.m_pos s hs
  rw [CircleParameterData.a, TailScaleCover.lower_intensity_eq _ _ _
    (Nat.cast_nonneg _) hm]
  have hatten := hp.attenuation_G (s - 1) (by omega)
  have heq : s - 1 + 1 = s := by omega
  rw [heq] at hatten
  exact (hp.L_monotone j (s - 1) hj (by omega)).trans hatten

theorem exists_tail_crossing_set (j : ℕ) (hj : 1 ≤ j) (k : ℤ)
    (hk : p.N j / 4 ≤ |(k : ℝ)|) :
    ∃ (s : ℕ) (w : ℝ) (I : Finset ℕ),
      j ≤ s ∧ (w = p.b s ∨ (j < s ∧ w = p.a s)) ∧
      I ⊆ p.block s ∧ (p.m s : ℝ) / 20 ≤ (I.card : ℝ) ∧
      (∀ i ∈ I, 1 - Int.fract ((k : ℝ) * p.alpha θ i) ∈ Set.Icc w (1 - w)) ∧
      p.L j ≤ (p.m s : ℝ) * (kappa s * Real.sqrt (w / (p.m s : ℝ))) ∧
      p.L j ≤ p.C s := by
  classical
  obtain ⟨s, hjs, htop, hleft⟩ := hp.tail_windows_cover j hj |(k : ℝ)| hk
  have hs : 1 ≤ s := hj.trans hjs
  have hcost : p.L j ≤ p.C s := by
    rw [hp.C_eq s hs]
    exact (hp.L_monotone j s hj hjs).trans (le_max_left _ _)
  by_cases hhigh : p.N s / 4 ≤ |(k : ℝ)|
  · let I := (p.block s).filter (fun i =>
      1 - Int.fract ((k : ℝ) * p.alpha θ i) ∈ Set.Icc (p.b s) (1 - p.b s))
    refine ⟨s, p.b s, I, hjs, Or.inl rfl, Finset.filter_subset _ _,
      hp.spread_high s hs k hhigh htop, ?_,
      hp.upper_crossing_intensity j s hj hjs, hcost⟩
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  · have hlow : j < s ∧ (p.G s : ℝ) * p.K s ≤ |(k : ℝ)| := by
      rcases hleft with ⟨hsj, hstart⟩ | hlow
      · exact False.elim (hhigh hstart)
      · exact hlow
    refine ⟨s, p.a s, p.block s, hjs, Or.inr ⟨hlow.1, rfl⟩,
      Finset.Subset.refl _, ?_, hp.spread_low s hs k hlow.2 (le_of_not_ge hhigh),
      hp.lower_crossing_intensity j s hj hlow.1, hcost⟩
    rw [p.card_block s hs]
    have hm : 0 ≤ (p.m s : ℝ) := Nat.cast_nonneg _
    linarith

end CircleParameterLaws
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FloorCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
namespace FloorCocycle

theorem floor_add_eq_indicator {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u < 1) (t : ℝ) :
    ⌊u + t⌋ = ⌊t⌋ + if 1 - Int.fract t ≤ u then 1 else 0 := by
  have hsplit : ⌊u + t⌋ = ⌊u + Int.fract t⌋ + ⌊t⌋ := by
    rw [← Int.floor_add_intCast]
    congr 1
    rw [add_assoc, Int.fract_add_floor]
  rw [hsplit]
  split_ifs with h
  · have hf : ⌊u + Int.fract t⌋ = 1 := by
      apply Int.floor_eq_iff.mpr
      constructor
      · norm_num
        linarith
      · norm_num
        linarith [Int.fract_lt_one t]
    rw [hf]
    omega
  · have hf : ⌊u + Int.fract t⌋ = 0 := by
      apply Int.floor_eq_zero_iff.mpr
      constructor
      · exact add_nonneg hu₀ (Int.fract_nonneg t)
      · linarith
    rw [hf]
    omega

theorem floor_sub_eq_crossing {u w : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u < 1) (hw₀ : 0 ≤ w) (hw₁ : w < 1)
    (huw : u ≤ w) (t : ℝ) :
    ⌊w + t⌋ - ⌊u + t⌋ =
      if u < 1 - Int.fract t ∧ 1 - Int.fract t ≤ w then 1 else 0 := by
  rw [floor_add_eq_indicator hw₀ hw₁, floor_add_eq_indicator hu₀ hu₁]
  by_cases huT : 1 - Int.fract t ≤ u
  · have hwT : 1 - Int.fract t ≤ w := huT.trans huw
    simp [huT, hwT, not_lt_of_ge huT]
  · have hut : u < 1 - Int.fract t := lt_of_not_ge huT
    by_cases hwT : 1 - Int.fract t ≤ w
    · simp [huT, hwT, hut]
    · simp [huT, hwT]

end FloorCocycle
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TaggedThresholdCrossing
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.FloorCocycle

theorem threshold_mem_Ioo_of_abs_phase {δ t : ℝ} (hδ : 0 ≤ δ)
    (hlo : δ < |t|) (hhi : |t| < 1 - δ) :
    1 - Int.fract t ∈ Set.Ioo δ (1 - δ) := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht] at hlo hhi
    have hf : Int.fract t = t := Int.fract_eq_self.mpr ⟨ht, by linarith⟩
    rw [hf]
    constructor <;> linarith
  · have ht' : t < 0 := lt_of_not_ge ht
    rw [abs_of_neg ht'] at hlo hhi
    have hf : Int.fract (-t) = -t :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hne : Int.fract (-t) ≠ 0 := by rw [hf]; linarith
    have hf' : Int.fract t = 1 + t := by
      simpa only [neg_neg, hf, sub_neg_eq_add] using Int.fract_neg hne
    rw [hf']
    constructor <;> linarith

theorem tagged_crossing_of_abs_phase {x y δ t : ℝ} (hδ : 0 ≤ δ)
    (hx : x < δ) (hy : 1 - δ < y)
    (hlo : δ < |t|) (hhi : |t| < 1 - δ) :
    x < 1 - Int.fract t ∧ 1 - Int.fract t ≤ y := by
  have h := threshold_mem_Ioo_of_abs_phase hδ hlo hhi
  exact ⟨hx.trans h.1, (h.2.trans hy).le⟩

theorem tagged_crossing_of_window {m K α x y : ℝ} (k : ℤ)
    (hm : 2 ≤ m) (hK : 0 < K)
    (hαlo : 1 / (m * K) < α) (hαhi : α < 2 / (m * K))
    (hklo : K < |(k : ℝ)|) (hkhi : |(k : ℝ)| ≤ m * K / 4)
    (hx : x < 1 / m) (hy : 1 - 1 / m < y) :
    x < 1 - Int.fract ((k : ℝ) * α) ∧
      1 - Int.fract ((k : ℝ) * α) ≤ y := by
  have hm0 : 0 < m := by linarith
  have hmK : 0 < m * K := mul_pos hm0 hK
  have hα0 : 0 < α := (one_div_pos.mpr hmK).trans hαlo
  have hk0 : 0 < |(k : ℝ)| := hK.trans hklo
  have hlo : 1 / m < |(k : ℝ)| * α := by
    calc
      1 / m = K * (1 / (m * K)) := by field_simp
      _ < |(k : ℝ)| * (1 / (m * K)) :=
        mul_lt_mul_of_pos_right hklo (one_div_pos.mpr hmK)
      _ ≤ |(k : ℝ)| * α := mul_le_mul_of_nonneg_left hαlo.le hk0.le
  have hhalf : |(k : ℝ)| * α < 1 / 2 := by
    calc
      |(k : ℝ)| * α < |(k : ℝ)| * (2 / (m * K)) :=
        mul_lt_mul_of_pos_left hαhi hk0
      _ ≤ (m * K / 4) * (2 / (m * K)) :=
        mul_le_mul_of_nonneg_right hkhi (div_nonneg (by norm_num) hmK.le)
      _ = 1 / 2 := by field_simp <;> ring
  have hinv : 1 / m ≤ (1 / 2 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hm
  apply tagged_crossing_of_abs_phase (one_div_pos.mpr hm0).le hx hy
  · simpa only [abs_mul, abs_of_pos hα0] using hlo
  · rw [abs_mul, abs_of_pos hα0]
    linarith

end Invariant233.FloorCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ConditionalKernelSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory

namespace Invariant233.CrossingAvoidance

variable {Ω β : Type*}

theorem ae_ae_condExpKernel_of_ae (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (hm' : m' ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    {P : Ω → Prop} (hP : ∀ᵐ ω ∂μ, P ω) :
    ∀ᵐ x ∂μ, ∀ᵐ ω ∂condExpKernel μ m' x, P ω := by
  apply ae_of_ae_trim hm'
  apply Measure.ae_ae_of_ae_comp
  rwa [condExpKernel_comp_trim hm']

theorem condExpKernel_ae_eq_of_measurable (m' : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    [mβ : MeasurableSpace β] [MeasurableEq β]
    (hm' : m' ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → β) (hf : Measurable[m'] f) :
    ∀ᵐ x ∂μ, ∀ᵐ ω ∂condExpKernel μ m' x, f ω = f x := by
  let : MeasurableSpace (Ω × Ω) := m'.prod mΩ
  have hf1 : @Measurable (Ω × Ω) β (m'.prod mΩ) mβ (fun z => f z.1) :=
    hf.comp (@measurable_fst Ω Ω m' mΩ)
  have hf2 : @Measurable (Ω × Ω) β (m'.prod mΩ) mβ (fun z => f z.2) :=
    (hf.mono hm' le_rfl).comp (@measurable_snd Ω Ω m' mΩ)
  have hdiag : @Measurable Ω (Ω × Ω) mΩ (m'.prod mΩ) (fun x => (x, x)) :=
    (measurable_id'' hm').prodMk measurable_id
  have hprod : ∀ᵐ z ∂(μ.trim hm') ⊗ₘ condExpKernel μ m', f z.2 = f z.1 := by
    rw [compProd_trim_condExpKernel hm']
    exact (ae_map_iff hdiag.aemeasurable (measurableSet_eq_fun hf2 hf1)).mpr
      (Filter.Eventually.of_forall (fun _ => rfl))
  exact ae_of_ae_trim hm' (Measure.ae_ae_of_ae_compProd hprod)

end Invariant233.CrossingAvoidance

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ConditionalCrossingAvoidance
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Invariant233.CrossingAvoidance

section KernelBounds

variable {ι Ω Y : Type*} [Countable ι] [MeasurableSpace Ω] [MeasurableSpace Y]

theorem kernel_iIndepSet_ae (κ : Kernel Y Ω) (ν : Measure Y)
    (events : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (events i))
    (hind : Kernel.iIndepSet events κ ν) :
    ∀ᵐ y ∂ν, iIndepSet events (κ y) := by
  have hall : ∀ᵐ y ∂ν, ∀ s : Finset ι,
      κ y (⋂ i ∈ s, events i) = ∏ i ∈ s, κ y (events i) :=
    ae_all_iff.mpr (fun s => hind.meas_biInter s)
  filter_upwards [hall] with y hy
  exact (iIndepSet_iff_meas_biInter hmeas).mpr hy

end KernelBounds

section ConditionalExpectation

variable {ι Ω : Type*} [Countable ι]

theorem iCondIndepSet_ae_condExpKernel (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (hm' : m' ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (events : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (events i))
    (hind : iCondIndepSet m' hm' events μ) :
    ∀ᵐ x ∂μ, iIndepSet events (condExpKernel μ m' x) := by
  exact ae_of_ae_trim hm'
    (@kernel_iIndepSet_ae ι Ω Ω ‹Countable ι› mΩ m'
      (condExpKernel μ m') (μ.trim hm') events hmeas hind)

theorem conditional_bad_le_exp_intensity (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (hm' : m' ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (events : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (events i))
    (hind : iCondIndepSet m' hm' events μ) (selected : Ω → Finset ι)
    (m ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : L ≤ m * ρ) (active : Ω → Prop)
    (hcard : ∀ᵐ x ∂μ, active x → m / 40 ≤ ((selected x).card : ℝ))
    (hp : ∀ᵐ x ∂μ, active x → ∀ i ∈ selected x,
      ρ / 10 ≤ (condExpKernel μ m' x).real (events i))
    (bad : Set Ω) (hbadmeas : MeasurableSet bad)
    (hzero : ∀ᵐ x ∂μ, ¬ active x → condExpKernel μ m' x bad = 0)
    (hbad : ∀ᵐ x ∂μ, ∀ᵐ ω ∂condExpKernel μ m' x,
      ω ∈ bad → ∀ i ∈ selected x, ω ∉ events i) :
    ∀ᵐ x ∂μ, (μ[bad.indicator (fun _ => (1 : ℝ)) | m']) x ≤
      Real.exp (-L / 400) := by
  filter_upwards [iCondIndepSet_ae_condExpKernel m' hm' μ events hmeas hind,
    hcard, hp, hzero, hbad, condExpKernel_ae_eq_condExp hm' hbadmeas]
    with x hx hcard hp hzero hbad heq
  rw [← heq]
  let : IsProbabilityMeasure (condExpKernel μ m' x) := hx.isProbabilityMeasure
  by_cases ha : active x
  · have hsubset : bad ≤ᵐ[condExpKernel μ m' x] ⋂ i ∈ selected x, (events i)ᶜ := by
      filter_upwards [hbad] with ω hω
      intro hb
      exact Set.mem_iInter.mpr (fun i => Set.mem_iInter.mpr (fun hi => hω hb i hi))
    have hmono : (condExpKernel μ m' x).real bad ≤
        (condExpKernel μ m' x).real (⋂ i ∈ selected x, (events i)ᶜ) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset)
    exact hmono.trans (measureReal_le_exp_intensity (condExpKernel μ m' x) events hx hmeas
      (selected x) m ρ L hρ (hcard ha) hL (hp ha) _ (Set.Subset.refl _))
  · change (condExpKernel μ m' x bad).toReal ≤ _
    rw [hzero ha, ENNReal.toReal_zero]
    exact (Real.exp_pos _).le

theorem conditional_bad_le_exp_of_endpoint {Y : Type*}
    (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    [MeasurableSpace Y] [MeasurableEq Y]
    (hm' : m' ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (events : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (events i))
    (hind : iCondIndepSet m' hm' events μ)
    (endpoint : Ω → Y) (hendpoint : Measurable[m'] endpoint)
    (selected : Y → Finset ι) (active : Y → Prop)
    (m ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : L ≤ m * ρ)
    (hcard : ∀ y, active y → m / 40 ≤ ((selected y).card : ℝ))
    (hp : ∀ᵐ x ∂μ, active (endpoint x) → ∀ i ∈ selected (endpoint x),
      ρ / 10 ≤ (μ[(events i).indicator (fun _ => (1 : ℝ)) | m']) x)
    (bad : Set Ω) (hbadmeas : MeasurableSet bad)
    (hbad : ∀ᵐ ω ∂μ, ω ∈ bad → active (endpoint ω) ∧
      ∀ i ∈ selected (endpoint ω), ω ∉ events i) :
    ∀ᵐ x ∂μ, (μ[bad.indicator (fun _ => (1 : ℝ)) | m']) x ≤
      Real.exp (-L / 400) := by
  have heq : ∀ᵐ x ∂μ, ∀ i, (condExpKernel μ m' x).real (events i) =
      (μ[(events i).indicator (fun _ => (1 : ℝ)) | m']) x :=
    ae_all_iff.mpr (fun i => condExpKernel_ae_eq_condExp hm' (hmeas i))
  have hpKernel : ∀ᵐ x ∂μ, active (endpoint x) → ∀ i ∈ selected (endpoint x),
      ρ / 10 ≤ (condExpKernel μ m' x).real (events i) := by
    filter_upwards [hp, heq] with x hx heq
    intro ha i hi
    rw [heq i]
    exact hx ha i hi
  have hfixed := condExpKernel_ae_eq_of_measurable m' hm' μ endpoint hendpoint
  have hlift := ae_ae_condExpKernel_of_ae m' hm' μ hbad
  have hsupport : ∀ᵐ x ∂μ, ∀ᵐ ω ∂condExpKernel μ m' x,
      ω ∈ bad → active (endpoint x) ∧ ∀ i ∈ selected (endpoint x), ω ∉ events i := by
    filter_upwards [hfixed, hlift] with x hfixed hlift
    filter_upwards [hfixed, hlift] with ω hfixed hlift
    intro hb
    simpa only [hfixed] using hlift hb
  have hzero : ∀ᵐ x ∂μ, ¬ active (endpoint x) → condExpKernel μ m' x bad = 0 := by
    filter_upwards [hsupport] with x hx
    intro ha
    have hn : ∀ᵐ ω ∂condExpKernel μ m' x, ω ∉ bad := by
      filter_upwards [hx] with ω hω
      exact fun hb => ha (hω hb).1
    simpa only [not_not, Set.ofPred_mem_eq] using (ae_iff.mp hn)
  have havoid : ∀ᵐ x ∂μ, ∀ᵐ ω ∂condExpKernel μ m' x,
      ω ∈ bad → ∀ i ∈ selected (endpoint x), ω ∉ events i := by
    filter_upwards [hsupport] with x hx
    filter_upwards [hx] with ω hω
    exact fun hb => (hω hb).2
  exact conditional_bad_le_exp_intensity m' hm' μ events hmeas hind
    (fun x => selected (endpoint x)) m ρ L hρ hL (fun x => active (endpoint x))
    (Filter.Eventually.of_forall (fun x => hcard (endpoint x))) hpKernel
    bad hbadmeas hzero havoid

end ConditionalExpectation

end Invariant233.CrossingAvoidance

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_FiniteConditionalAttenuation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace Invariant233.CrossingAvoidance

variable {ι Ω : Type*}

theorem measurable_card_filter [MeasurableSpace Ω] (s : Finset ι)
    (p : Ω → ι → Prop)
    (hp : ∀ i ∈ s, MeasurableSet {ω | p ω i}) :
    Measurable (fun ω => (s.filter (fun i => p ω i)).card) := by
  classical
  have hsum : Measurable (fun ω => ∑ i ∈ s, if p ω i then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (hp i hi) measurable_const measurable_const
  simpa only [Finset.sum_boole, Nat.cast_id] using hsum

theorem finite_conditional_attenuation [Countable ι]
    (mx my : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (hmx : mx ≤ mΩ) (hmy : my ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (I : Finset ι) (u : ι → ℝ) (x y : Ω → ι → ℝ)
    (hx : Measurable[mx] x) (hy : Measurable[my] y)
    (top bottom : ι → Set Ω)
    (htop : ∀ i, MeasurableSet (top i)) (hbottom : ∀ i, MeasurableSet (bottom i))
    (hindTop : iCondIndepSet mx hmx top μ) (hindBottom : iCondIndepSet my hmy bottom μ)
    (m ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : L ≤ m * ρ)
    (hI : m / 20 ≤ (I.card : ℝ))
    (horder : ∀ᵐ ω ∂μ, ∀ i ∈ I, x ω i ≤ y ω i)
    (hforceTop : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      x ω i < u i → ω ∈ top i → u i ≤ y ω i)
    (hforceBottom : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      u i ≤ y ω i → ω ∈ bottom i → x ω i < u i)
    (hprobTop : ∀ᵐ ω ∂μ, ∀ i ∈ I, x ω i < u i →
      ρ / 10 ≤ (μ[(top i).indicator (fun _ => (1 : ℝ)) | mx]) ω)
    (hprobBottom : ∀ᵐ ω ∂μ, ∀ i ∈ I, u i ≤ y ω i →
      ρ / 10 ≤ (μ[(bottom i).indicator (fun _ => (1 : ℝ)) | my]) ω)
    (R : Ω → ℝ) (hR : ∀ᵐ ω ∂μ, R ω ≤ 1)
    (hcross : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      (x ω i < u i ∧ u i ≤ y ω i) → R ω ≤ Real.exp (-L)) :
    ∃ H₁ H₂ : Set Ω, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂μ, (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂μ, (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂μ, R ω ≤ Real.exp (-L) + H₁.indicator (fun _ => (1 : ℝ)) ω +
        H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  classical
  let B : Set Ω := {ω | ∀ i ∈ I, ¬ (x ω i < u i ∧ u i ≤ y ω i)}
  let low : (ι → ℝ) → Finset ι := fun a => I.filter (fun i => a i < u i)
  let high : (ι → ℝ) → Finset ι := fun a => I.filter (fun i => u i ≤ a i)
  let activeLow : (ι → ℝ) → Prop := fun a => I.card ≤ 2 * (low a).card
  let activeHigh : (ι → ℝ) → Prop := fun a => I.card ≤ 2 * (high a).card
  let H₁ : Set Ω := B ∩ {ω | activeLow (x ω)}
  let H₂ : Set Ω := B \ {ω | activeLow (x ω)}
  have hxi (i : ι) : Measurable (fun ω => x ω i) :=
    (measurable_pi_apply i).comp (hx.mono hmx le_rfl)
  have hyi (i : ι) : Measurable (fun ω => y ω i) :=
    (measurable_pi_apply i).comp (hy.mono hmy le_rfl)
  have hB : MeasurableSet B := by
    have hh : MeasurableSet (⋂ i ∈ I, {ω | ¬ (x ω i < u i ∧ u i ≤ y ω i)}) :=
      MeasurableSet.biInter I.countable_toSet (fun i _ =>
        ((measurableSet_lt (hxi i) measurable_const).inter
          (measurableSet_le measurable_const (hyi i))).compl)
    simpa only [B, Set.ofPred_forall] using hh
  have hcount : Measurable (fun ω => (low (x ω)).card) := by
    apply measurable_card_filter I (fun ω i => x ω i < u i)
    intro i _
    exact measurableSet_lt (hxi i) measurable_const
  have hactive : MeasurableSet {ω | activeLow (x ω)} :=
    measurableSet_le measurable_const (measurable_const.mul hcount)
  have hH₁ : MeasurableSet H₁ := hB.inter hactive
  have hH₂ : MeasurableSet H₂ := hB.diff hactive
  have hbound₁ : ∀ᵐ ω ∂μ,
      (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ Real.exp (-L / 400) := by
    apply conditional_bad_le_exp_of_endpoint mx hmx μ top htop hindTop x hx
      low activeLow m ρ L hρ hL
    · intro a ha
      exact eligible_card_lower_bound I (low a) m hI ha
    · filter_upwards [hprobTop] with ω hω
      intro _ i hi
      have hi' := Finset.mem_filter.mp hi
      exact hω i hi'.1 hi'.2
    · exact hH₁
    · filter_upwards [hforceTop] with ω hω
      intro hmem
      refine ⟨hmem.2, ?_⟩
      intro i hi hlabel
      have hi' := Finset.mem_filter.mp hi
      exact hmem.1 i hi'.1 ⟨hi'.2, hω i hi'.1 hi'.2 hlabel⟩
  have hbound₂ : ∀ᵐ ω ∂μ,
      (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ Real.exp (-L / 400) := by
    apply conditional_bad_le_exp_of_endpoint my hmy μ bottom hbottom hindBottom y hy
      high activeHigh m ρ L hρ hL
    · intro a ha
      exact eligible_card_lower_bound I (high a) m hI ha
    · filter_upwards [hprobBottom] with ω hω
      intro _ i hi
      have hi' := Finset.mem_filter.mp hi
      exact hω i hi'.1 hi'.2
    · exact hH₂
    · filter_upwards [horder, hforceBottom] with ω horder hω
      intro hmem
      have hhalf : activeHigh (y ω) :=
        above_half_of_below_not_half I (x ω) (y ω) u horder hmem.1 hmem.2
      refine ⟨hhalf, ?_⟩
      intro i hi hlabel
      have hi' := Finset.mem_filter.mp hi
      exact hmem.1 i hi'.1 ⟨hω i hi'.1 hi'.2 hlabel, hi'.2⟩
  refine ⟨H₁, H₂, hH₁, hH₂, hbound₁, hbound₂, ?_⟩
  filter_upwards [hR, hcross] with ω hR hcross
  by_cases hb : ω ∈ B
  · by_cases ha : activeLow (x ω)
    · have h1 : ω ∈ H₁ := ⟨hb, ha⟩
      have h2 : ω ∉ H₂ := fun h => h.2 ha
      rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
      linarith [Real.exp_pos (-L)]
    · have h1 : ω ∉ H₁ := fun h => ha h.2
      have h2 : ω ∈ H₂ := ⟨hb, ha⟩
      rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2]
      linarith [Real.exp_pos (-L)]
  · have hb' : ¬ ∀ i ∈ I, ¬ (x ω i < u i ∧ u i ≤ y ω i) := hb
    push Not at hb'
    obtain ⟨i, hi, hci⟩ := hb'
    have h1 : ω ∉ H₁ := fun h => hb h.1
    have h2 : ω ∉ H₂ := fun h => hb h.1
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    simpa using hcross i hi hci

theorem empty_exceptional_events (mx my : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} (μ : Measure Ω) (E : Set Ω) (R : Ω → ℝ)
    (η δ : ℝ) (hδ : 0 ≤ δ)
    (hR : ∀ᵐ ω ∂μ, ω ∈ E → R ω ≤ η) :
    ∃ H₁ H₂ : Set Ω, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂μ, (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ δ) ∧
      (∀ᵐ ω ∂μ, (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ δ) ∧
      (∀ᵐ ω ∂μ, ω ∈ E → R ω ≤ η + H₁.indicator (fun _ => (1 : ℝ)) ω +
        H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  refine ⟨∅, ∅, MeasurableSet.empty, MeasurableSet.empty, ?_, ?_, ?_⟩
  · simp only [Set.indicator_empty, condExp_fun_zero]
    exact Filter.Eventually.of_forall (fun _ => hδ)
  · simp only [Set.indicator_empty, condExp_fun_zero]
    exact Filter.Eventually.of_forall (fun _ => hδ)
  · simpa only [Set.indicator_empty, Pi.zero_apply, add_zero] using hR

end Invariant233.CrossingAvoidance

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FiniteSupportWeights
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal

namespace Invariant233.FiniteSupportWeights

variable {X ι κ : Type*} [MeasurableSpace X]

theorem uniform_nonzero_floor_of_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)) {u | Int.floor (u + t) ≠ 0} =
      ENNReal.ofReal t := by
  have hmeas : MeasurableSet {u : ℝ | Int.floor (u + t) ≠ 0} :=
    (measurableSet_eq_fun (measurable_id.add_const t).floor measurable_const).compl
  rw [Measure.restrict_apply hmeas]
  have hset : {u : ℝ | Int.floor (u + t) ≠ 0} ∩ Set.Ico 0 1 =
      Set.Ico (1 - t) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ne_eq, Int.floor_eq_zero_iff,
      Set.mem_Ico]
    constructor
    · rintro ⟨hn, hu0, hu1⟩
      refine ⟨?_, hu1⟩
      by_contra h
      apply hn
      constructor <;> linarith
    · rintro ⟨hu0, hu1⟩
      refine ⟨?_, ?_, hu1⟩
      · intro h
        linarith [h.2]
      · linarith
  rw [hset, Real.volume_Ico]
  congr 1
  ring

theorem uniform_nonzero_floor_of_nonpos {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 0) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)) {u | Int.floor (u + t) ≠ 0} =
      ENNReal.ofReal (-t) := by
  have hmeas : MeasurableSet {u : ℝ | Int.floor (u + t) ≠ 0} :=
    (measurableSet_eq_fun (measurable_id.add_const t).floor measurable_const).compl
  rw [Measure.restrict_apply hmeas]
  have hset : {u : ℝ | Int.floor (u + t) ≠ 0} ∩ Set.Ico 0 1 =
      Set.Ico 0 (-t) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ne_eq, Int.floor_eq_zero_iff,
      Set.mem_Ico]
    constructor
    · rintro ⟨hn, hu0, hu1⟩
      refine ⟨hu0, ?_⟩
      by_contra h
      apply hn
      constructor <;> linarith
    · rintro ⟨hu0, hu1⟩
      refine ⟨?_, hu0, ?_⟩
      · intro h
        linarith [h.1]
      · linarith
  rw [hset, Real.volume_Ico, sub_zero]

theorem uniform_nonzero_floor_le (t : ℝ) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)) {u | Int.floor (u + t) ≠ 0} ≤
      ENNReal.ofReal |t| := by
  by_cases ht : |t| ≤ 1
  · have ht' := abs_le.mp ht
    rcases le_total 0 t with hpos | hneg
    · rw [uniform_nonzero_floor_of_nonneg hpos ht'.2, abs_of_nonneg hpos]
    · rw [uniform_nonzero_floor_of_nonpos ht'.1 hneg, abs_of_nonpos hneg]
  · calc
      _ ≤ (volume.restrict (Set.Ico (0 : ℝ) 1)) Set.univ := measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal |t| := ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_not_ge ht))

theorem measure_nonzero_floor_le (μ : Measure X) (u : X → ℝ)
    (hu : MeasurePreserving u μ (volume.restrict (Set.Ico (0 : ℝ) 1))) (t : ℝ) :
    μ {x | Int.floor (u x + t) ≠ 0} ≤ ENNReal.ofReal |t| := by
  have hmeas : MeasurableSet {v : ℝ | Int.floor (v + t) ≠ 0} :=
    (measurableSet_eq_fun (measurable_id.add_const t).floor measurable_const).compl
  change μ (u ⁻¹' {v : ℝ | Int.floor (v + t) ≠ 0}) ≤ _
  rw [hu.measure_preimage hmeas.nullMeasurableSet]
  exact uniform_nonzero_floor_le t

theorem ae_finite_floor_support [Countable ι] (μ : Measure X) (u : ι → X → ℝ)
    (hu : ∀ i, MeasurePreserving (u i) μ (volume.restrict (Set.Ico (0 : ℝ) 1)))
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) (k : ℤ) :
    ∀ᵐ x ∂μ, (Function.support (fun i => Int.floor (u i x + (k : ℝ) * α i))).Finite := by
  have hs : Summable (fun i => |(k : ℝ)| * α i) := hα.mul_left _
  have hbound : (∑' i, μ {x | Int.floor (u i x + (k : ℝ) * α i) ≠ 0}) ≤
      ∑' i, ENNReal.ofReal (|(k : ℝ)| * α i) := by
    apply ENNReal.tsum_le_tsum
    intro i
    simpa only [abs_mul, abs_of_nonneg (hα0 i)] using
      measure_nonzero_floor_le μ (u i) (hu i) ((k : ℝ) * α i)
  exact ae_finite_setOfPred_mem (lt_of_le_of_lt hbound hs.tsum_ofReal_lt_top).ne

theorem ae_all_finite_floor_support [Countable ι] (μ : Measure X) (u : ι → X → ℝ)
    (hu : ∀ i, MeasurePreserving (u i) μ (volume.restrict (Set.Ico (0 : ℝ) 1)))
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) :
    ∀ᵐ x ∂μ, ∀ k : ℤ,
      (Function.support (fun i => Int.floor (u i x + (k : ℝ) * α i))).Finite := by
  exact ae_all_iff.mpr fun k => ae_finite_floor_support μ u hu α hα0 hα k

end Invariant233.FiniteSupportWeights

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleWeightSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.CircleWeightSupport

theorem ae_all_int_finite_floor_support {ι : Type*} [Countable ι]
    (q : ι → ℤ) (hq : ∀ i, q i ≠ 0)
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) :
    ∀ᵐ x ∂(volume : Measure UnitAddCircle), ∀ k : ℤ,
      (Function.support (fun i =>
        Int.floor (((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ) +
          (k : ℝ) * α i))).Finite := by
  exact FiniteSupportWeights.ae_all_finite_floor_support volume
    (fun i x => ((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ))
    (fun i => measurePreserving_characterRepresentative (q i) (hq i)) α hα0 hα

end Invariant233.CircleWeightSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FiniteSupportCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Function

namespace Invariant233.FiniteSupportCocycle

theorem summable_weighted_int {I : Type*} (c : I → ℝ) {a : I → ℤ}
    (ha : HasFiniteSupport a) : Summable (fun i ↦ c i * (a i : ℝ)) := by
  apply summable_of_hasFiniteSupport
  exact HasFiniteSupport.mul_right c (ha.fun_comp (by simp))

theorem exp_tsum_floor_ratio_le_one {I : Type*} (x y θ c : I → ℝ) (k : ℤ)
    (hc : ∀ i, 0 ≤ c i) (hxy : ∀ i, x i ≤ y i)
    (hx : HasFiniteSupport (fun i ↦ ⌊x i + (k : ℝ) * θ i⌋))
    (hy : HasFiniteSupport (fun i ↦ ⌊y i + (k : ℝ) * θ i⌋)) :
    Real.exp (-(∑' i, c i * (⌊y i + (k : ℝ) * θ i⌋ : ℝ))) /
      Real.exp (-(∑' i, c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ))) ≤ 1 := by
  rw [← Real.exp_sub, Real.exp_le_one_iff]
  have hsum : (∑' i, c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ)) ≤
      ∑' i, c i * (⌊y i + (k : ℝ) * θ i⌋ : ℝ) := by
    apply Summable.tsum_le_tsum _ (summable_weighted_int c hx) (summable_weighted_int c hy)
    intro i
    apply mul_le_mul_of_nonneg_left _ (hc i)
    exact Int.cast_le.mpr (Int.floor_mono (add_le_add_left (hxy i) ((k : ℝ) * θ i)))
  linarith

theorem exp_tsum_floor_ratio_eq_crossings {I : Type*} (x y t c : I → ℝ)
    (hx01 : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy01 : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1)
    (hxy : ∀ i, x i ≤ y i)
    (hx : HasFiniteSupport (fun i ↦ ⌊x i + t i⌋))
    (hy : HasFiniteSupport (fun i ↦ ⌊y i + t i⌋)) :
    Real.exp (-(∑' i, c i * (⌊y i + t i⌋ : ℝ))) /
      Real.exp (-(∑' i, c i * (⌊x i + t i⌋ : ℝ))) =
      Real.exp (-(∑' i, if x i < 1 - Int.fract (t i) ∧
        1 - Int.fract (t i) ≤ y i then c i else 0)) := by
  classical
  have hcoord (i : I) :
      c i * (⌊y i + t i⌋ : ℝ) - c i * (⌊x i + t i⌋ : ℝ) =
        if x i < 1 - Int.fract (t i) ∧ 1 - Int.fract (t i) ≤ y i then c i else 0 := by
    rw [← mul_sub, ← Int.cast_sub,
      FloorCocycle.floor_sub_eq_crossing (hx01 i).1 (hx01 i).2
        (hy01 i).1 (hy01 i).2 (hxy i)]
    split_ifs <;> simp
  rw [← Real.exp_sub]
  congr 1
  rw [show -(∑' i, c i * (⌊y i + t i⌋ : ℝ)) -
      -(∑' i, c i * (⌊x i + t i⌋ : ℝ)) =
      -((∑' i, c i * (⌊y i + t i⌋ : ℝ)) -
        ∑' i, c i * (⌊x i + t i⌋ : ℝ)) by ring]
  rw [← (summable_weighted_int c hy).tsum_sub (summable_weighted_int c hx)]
  congr 1
  exact tsum_congr hcoord

theorem exp_tsum_floor_ratio_le_finite_crossings {I : Type*}
    (x y t c : I → ℝ) (s : Finset I)
    (hx01 : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy01 : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hxy : ∀ i, x i ≤ y i)
    (hx : HasFiniteSupport (fun i ↦ ⌊x i + t i⌋))
    (hy : HasFiniteSupport (fun i ↦ ⌊y i + t i⌋))
    (hcross : ∀ i ∈ s, x i < 1 - Int.fract (t i) ∧
      1 - Int.fract (t i) ≤ y i) :
    Real.exp (-(∑' i, c i * (⌊y i + t i⌋ : ℝ))) /
      Real.exp (-(∑' i, c i * (⌊x i + t i⌋ : ℝ))) ≤
      Real.exp (-∑ i ∈ s, c i) := by
  classical
  let d : I → ℝ := fun i ↦
    if x i < 1 - Int.fract (t i) ∧ 1 - Int.fract (t i) ≤ y i then c i else 0
  have hd_eq (i : I) :
      c i * (⌊y i + t i⌋ : ℝ) - c i * (⌊x i + t i⌋ : ℝ) = d i := by
    rw [← mul_sub, ← Int.cast_sub,
      FloorCocycle.floor_sub_eq_crossing (hx01 i).1 (hx01 i).2
        (hy01 i).1 (hy01 i).2 (hxy i)]
    dsimp [d]
    split_ifs <;> simp
  have hd : Summable d :=
    ((summable_weighted_int c hy).sub (summable_weighted_int c hx)).congr hd_eq
  have hd_nonneg (i : I) : 0 ≤ d i := by
    dsimp [d]
    split_ifs <;> simp_all only [le_refl]
  have hbound : (∑ i ∈ s, c i) ≤ ∑' i, d i := by
    calc
      (∑ i ∈ s, c i) = ∑ i ∈ s, d i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [d, ite_eq_left (hcross i hi)]
      _ ≤ ∑' i, d i := hd.sum_le_tsum s (fun i _ ↦ hd_nonneg i)
  rw [exp_tsum_floor_ratio_eq_crossings x y t c hx01 hy01 hxy hx hy]
  apply Real.exp_le_exp.mpr
  exact neg_le_neg hbound

end Invariant233.FiniteSupportCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function

namespace Invariant233.CircleWeights

variable {ι : Type*}

theorem coordinate_mem_Ico (q : ι → ℤ) (i : ι) (x : UnitAddCircle) :
    coordinate q i x ∈ Ico (0 : ℝ) 1 := by
  simpa only [coordinate, representative, zero_add] using
    (AddCircle.equivIco (1 : ℝ) 0 (q i • x)).property

end Invariant233.CircleWeights

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleParameterConsequences
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
open Filter
open scoped Topology

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem shifted_K_pos (n : ℕ) : 0 < (p.K (n + 1) : ℝ) := by
  exact_mod_cast hp.K_pos (n + 1) (by omega)

theorem shifted_K_double (n : ℕ) :
    2 * (p.K (n + 1) : ℝ) ≤ (p.K (n + 1 + 1) : ℝ) := by
  exact_mod_cast (hp.K_double (n + 1) (by omega)).le

theorem summable_reciprocal : Summable (fun n : ℕ => 1 / (p.K (n + 1) : ℝ)) :=
  ParameterTails.summable_reciprocal hp.shifted_K_pos hp.shifted_K_double

end CircleParameterLaws
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CirclePhaseSummability
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
open scoped BigOperators ENNReal

namespace CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem block_phase_sum_le (j : ℕ) (hj : 1 ≤ j) :
    (∑ i ∈ p.block j, p.alpha θ i) ≤ 2 / (p.K j : ℝ) := by
  have hm : (p.m j : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos j hj).ne'
  have hK : (p.K j : ℝ) ≠ 0 := by exact_mod_cast (hp.K_pos j hj).ne'
  calc
    (∑ i ∈ p.block j, p.alpha θ i) ≤ ∑ i ∈ p.block j, 2 / p.N j := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hp.phase_bounds j hj i hi).2.le
    _ = ((p.block j).card : ℝ) * (2 / p.N j) := by simp
    _ = 2 / (p.K j : ℝ) := by
      rw [p.card_block j hj]
      simp only [CircleParameterData.N]
      field_simp

theorem summable_block_phases :
    Summable (fun n : ℕ => ∑ i ∈ p.block (n + 1), p.alpha θ i) := by
  apply Summable.of_nonneg_of_le
    (fun n => Finset.sum_nonneg (fun i _ => Int.fract_nonneg _))
    (fun n => hp.block_phase_sum_le (n + 1) (by omega))
  simpa only [mul_one_div] using hp.summable_reciprocal.mul_left 2

end CircleParameterLaws
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ParameterCircleCocycle
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function
open scoped BigOperators ENNReal

namespace Invariant233

namespace CircleParameterData

theorem coord_phase_eq (p : CircleParameterData) (θ : ℝ) (i : p.Coord) :
    CircleWeights.phase θ p.coordFrequency i = p.alpha θ i.2 := by
  simp only [CircleWeights.phase, coordFrequency, alpha, Int.cast_natCast]

theorem coord_coordinate_eq (p : CircleParameterData) (i : p.Coord) (x : Circle) :
    CircleWeights.coordinate p.coordFrequency i x = p.coordinate i.2 x := by
  simp only [CircleWeights.coordinate, CircleWeights.representative,
    coordFrequency, coordinate, rep, natCast_zsmul]

end CircleParameterData

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem summable_coord_phases : Summable (CircleWeights.phase θ p.coordFrequency) := by
  rw [show CircleWeights.phase θ p.coordFrequency =
    (fun i : p.Coord => p.alpha θ i.2) from funext (p.coord_phase_eq θ)]
  apply (summable_sigma_of_nonneg (fun i => Int.fract_nonneg _)).mpr
  constructor
  · intro j
    exact (hasSum_fintype _).summable
  · apply hp.summable_block_phases.congr
    intro j
    simp only [tsum_fintype]
    exact (Finset.sum_attach (p.block (j + 1)) (p.alpha θ)).symm

end CircleParameterLaws
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleConditionalAttenuation
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Function Set
open scoped BigOperators

namespace Invariant233.CircleWeights

theorem cocycle_ratio_le_exp_of_crossing {ι : Type*}
    (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ) (k : ℤ) (x y : UnitAddCircle) (i : ι)
    (hc : ∀ j, 0 ≤ c j) (horder : ∀ j, coordinate q j x ≤ coordinate q j y)
    (hx : HasFiniteSupport (fun j => ⌊coordinate q j x + (k : ℝ) * phase θ q j⌋))
    (hy : HasFiniteSupport (fun j => ⌊coordinate q j y + (k : ℝ) * phase θ q j⌋))
    (hcross : coordinate q i x < 1 - Int.fract ((k : ℝ) * phase θ q i) ∧
      1 - Int.fract ((k : ℝ) * phase θ q i) ≤ coordinate q i y) :
    cocycle θ q c k y / cocycle θ q c k x ≤ Real.exp (-c i) := by
  classical
  have h := FiniteSupportCocycle.exp_tsum_floor_ratio_le_finite_crossings
    (fun j => coordinate q j x) (fun j => coordinate q j y)
    (fun j => (k : ℝ) * phase θ q j) c {i}
    (fun j => coordinate_mem_Ico q j x) (fun j => coordinate_mem_Ico q j y)
    hc horder hx hy (by simpa using hcross)
  simpa only [cocycle, floorCost, Finset.sum_singleton] using h

theorem ae_all_int_finite_floor_support_of_map_ac
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (θ : ℝ) (q : ι → ℤ) (hq : ∀ i, q i ≠ 0)
    (hphase : Summable (phase θ q))
    (x : Ω → UnitAddCircle) (hx : AEMeasurable x μ)
    (hac : μ.map x ≪ (volume : Measure UnitAddCircle)) :
    ∀ᵐ ω ∂μ, ∀ k : ℤ,
      HasFiniteSupport (fun i => ⌊coordinate q i (x ω) + (k : ℝ) * phase θ q i⌋) := by
  apply ae_of_ae_map hx (p := fun z : UnitAddCircle => ∀ k : ℤ,
    HasFiniteSupport (fun i => ⌊coordinate q i z + (k : ℝ) * phase θ q i⌋))
  exact hac.ae_le (CircleWeightSupport.ae_all_int_finite_floor_support q hq
    (phase θ q) (phase_nonneg θ q) hphase)

theorem ae_all_int_ratio_bounds_of_map_ac
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (θ : ℝ) (q : ι → ℤ) (hq : ∀ i, q i ≠ 0)
    (hphase : Summable (phase θ q)) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (x y : Ω → UnitAddCircle) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hacx : μ.map x ≪ (volume : Measure UnitAddCircle))
    (hacy : μ.map y ≪ (volume : Measure UnitAddCircle))
    (horder : ∀ᵐ ω ∂μ, ∀ i, coordinate q i (x ω) ≤ coordinate q i (y ω)) :
    ∀ᵐ ω ∂μ, ∀ k : ℤ,
      cocycle θ q c k (y ω) / cocycle θ q c k (x ω) ≤ 1 ∧
      ∀ i, (coordinate q i (x ω) < 1 - Int.fract ((k : ℝ) * phase θ q i) ∧
        1 - Int.fract ((k : ℝ) * phase θ q i) ≤ coordinate q i (y ω)) →
      cocycle θ q c k (y ω) / cocycle θ q c k (x ω) ≤ Real.exp (-c i) := by
  filter_upwards [ae_all_int_finite_floor_support_of_map_ac μ θ q hq hphase x hx hacx,
    ae_all_int_finite_floor_support_of_map_ac μ θ q hq hphase y hy hacy, horder]
    with ω hxs hys hord
  intro k
  refine ⟨?_, fun i hi => cocycle_ratio_le_exp_of_crossing θ q c k (x ω) (y ω) i
    hc hord (hxs k) (hys k) hi⟩
  exact FiniteSupportCocycle.exp_tsum_floor_ratio_le_one
    (fun i => coordinate q i (x ω)) (fun i => coordinate q i (y ω))
    (phase θ q) c k hc hord (hxs k) (hys k)

end Invariant233.CircleWeights

namespace Invariant233.CircleParameterLaws

theorem ae_parameter_ratio_bounds_of_map_ac
    {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x y : Ω → Circle) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hacx : μ.map x ≪ circleMeasure) (hacy : μ.map y ≪ circleMeasure)
    (horder : ∀ᵐ ω ∂μ, ∀ i : p.Coord, p.coordinate i.2 (x ω) ≤ p.coordinate i.2 (y ω)) :
    ∀ᵐ ω ∂μ, ∀ k : ℤ,
      p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω) ≤ 1 ∧
      ∀ i : p.Coord,
        (p.coordinate i.2 (x ω) < 1 - Int.fract ((k : ℝ) * p.alpha θ i.2) ∧
          1 - Int.fract ((k : ℝ) * p.alpha θ i.2) ≤ p.coordinate i.2 (y ω)) →
        p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω) ≤ Real.exp (-p.coordCost i) := by
  have hord : ∀ᵐ ω ∂μ, ∀ i : p.Coord,
      CircleWeights.coordinate p.coordFrequency i (x ω) ≤
        CircleWeights.coordinate p.coordFrequency i (y ω) := by
    simpa only [p.coord_coordinate_eq] using horder
  simpa only [CircleParameterData.floorCocycle, p.coord_coordinate_eq, p.coord_phase_eq] using
    CircleWeights.ae_all_int_ratio_bounds_of_map_ac μ θ p.coordFrequency
      hp.coordFrequency_ne_zero hp.summable_coord_phases p.coordCost
      (fun i => (hp.coordCost_pos i).le) x y hx hy hacx hacy hord

theorem ae_parameter_tagged_ratio_le_exp
    {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x y : Ω → Circle) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hacx : μ.map x ≪ circleMeasure) (hacy : μ.map y ≪ circleMeasure)
    (horder : ∀ᵐ ω ∂μ, ∀ i : p.Coord, p.coordinate i.2 (x ω) ≤ p.coordinate i.2 (y ω))
    (j : ℕ) (hj : 1 ≤ j) (k : ℤ)
    (hklo : (p.K j : ℝ) < |(k : ℝ)|) (hkhi : |(k : ℝ)| ≤ p.N j / 4)
    (E : Set Ω) (htag : ∀ᵐ ω ∂μ, ω ∈ E → ∃ i ∈ p.block j,
      p.coordinate i (x ω) < 1 / (p.m j : ℝ) ∧
        1 - 1 / (p.m j : ℝ) < p.coordinate i (y ω)) :
    ∀ᵐ ω ∂μ, ω ∈ E →
      p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω) ≤ Real.exp (-p.L j) := by
  filter_upwards [hp.ae_parameter_ratio_bounds_of_map_ac μ x y hx hy hacx hacy horder,
    htag] with ω hr ht
  intro hE
  obtain ⟨i, hi, hxi, hyi⟩ := ht hE
  have hj' : j - 1 + 1 = j := by omega
  let a : p.Coord := ⟨j - 1, ⟨i, by simpa only [hj'] using hi⟩⟩
  have hm : (2 : ℝ) ≤ (p.m j : ℝ) := by exact_mod_cast (le_trans (by norm_num) (hp.m_ge_200 j hj))
  have hK : (0 : ℝ) < (p.K j : ℝ) := by exact_mod_cast hp.K_pos j hj
  have hphase := hp.phase_bounds j hj i hi
  have hcross := FloorCocycle.tagged_crossing_of_window k hm hK
    hphase.1 hphase.2 hklo hkhi hxi hyi
  have hratio := (hr k).2 a hcross
  have hcost : p.L j ≤ p.coordCost a := by
    change p.L j ≤ p.C (j - 1 + 1)
    rw [hj', hp.C_eq j hj]
    exact le_max_left _ _
  exact hratio.trans (Real.exp_le_exp.mpr (neg_le_neg hcost))

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ParameterTailAttenuation
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace Invariant233.CircleParameterLaws
open CircleParameterData

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem measurable_parameter_coordinate (i : ℕ) : Measurable (p.coordinate i) := by
  have hq : (p.q i : ℤ) ≠ 0 := by exact_mod_cast (hp.q_pos i).ne'
  change Measurable (fun x : UnitAddCircle =>
    ((AddCircle.equivIco (1 : ℝ) 0 (p.q i • x)) : ℝ))
  simpa only [natCast_zsmul] using
    (CircleWeightSupport.measurePreserving_characterRepresentative (p.q i) hq).measurable

theorem finite_parameter_conditional_attenuation
    {Ω : Type*} (mx my : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (hmx : mx ≤ mΩ) (hmy : my ≤ mΩ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (x y : Ω → Circle) (hx : Measurable[mx] x) (hy : Measurable[my] y)
    (hacx : μ.map x ≪ circleMeasure) (hacy : μ.map y ≪ circleMeasure)
    (horder : ∀ᵐ ω ∂μ, ∀ i : p.Coord,
      p.coordinate i.2 (x ω) ≤ p.coordinate i.2 (y ω))
    (top bottom : ℕ → Set Ω)
    (htop : ∀ i, MeasurableSet (top i)) (hbottom : ∀ i, MeasurableSet (bottom i))
    (hindTop : iCondIndepSet mx hmx top μ) (hindBottom : iCondIndepSet my hmy bottom μ)
    (s : ℕ) (hs : 1 ≤ s) (k : ℤ) (I : Finset ℕ) (hIs : I ⊆ p.block s)
    (hI : (p.m s : ℝ) / 20 ≤ (I.card : ℝ))
    (ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : L ≤ (p.m s : ℝ) * ρ) (hcost : L ≤ p.C s)
    (hforceTop : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      p.coordinate i (x ω) < 1 - Int.fract ((k : ℝ) * p.alpha θ i) →
      ω ∈ top i → 1 - Int.fract ((k : ℝ) * p.alpha θ i) ≤ p.coordinate i (y ω))
    (hforceBottom : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      1 - Int.fract ((k : ℝ) * p.alpha θ i) ≤ p.coordinate i (y ω) →
      ω ∈ bottom i → p.coordinate i (x ω) < 1 - Int.fract ((k : ℝ) * p.alpha θ i))
    (hprobTop : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      p.coordinate i (x ω) < 1 - Int.fract ((k : ℝ) * p.alpha θ i) →
      ρ / 10 ≤ (μ[(top i).indicator (fun _ => (1 : ℝ)) | mx]) ω)
    (hprobBottom : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      1 - Int.fract ((k : ℝ) * p.alpha θ i) ≤ p.coordinate i (y ω) →
      ρ / 10 ≤ (μ[(bottom i).indicator (fun _ => (1 : ℝ)) | my]) ω) :
    ∃ H₁ H₂ : Set Ω, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂μ, (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂μ, (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂μ, p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω) ≤
        Real.exp (-L) + H₁.indicator (fun _ => (1 : ℝ)) ω +
          H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  have hs' : s - 1 + 1 = s := by omega
  let coord (i : ℕ) (hi : i ∈ I) : p.Coord :=
    ⟨s - 1, ⟨i, by simpa only [hs'] using hIs hi⟩⟩
  have hxrep : Measurable[mx] (fun ω i => p.coordinate i (x ω)) := by
    let : MeasurableSpace Ω := mx
    exact Measurable.of_eval (fun i => (hp.measurable_parameter_coordinate i).comp hx)
  have hyrep : Measurable[my] (fun ω i => p.coordinate i (y ω)) := by
    let : MeasurableSpace Ω := my
    exact Measurable.of_eval (fun i => (hp.measurable_parameter_coordinate i).comp hy)
  have hr := hp.ae_parameter_ratio_bounds_of_map_ac μ x y
    (hx.mono hmx le_rfl).aemeasurable (hy.mono hmy le_rfl).aemeasurable hacx hacy horder
  apply CrossingAvoidance.finite_conditional_attenuation mx my hmx hmy μ I
    (fun i => 1 - Int.fract ((k : ℝ) * p.alpha θ i))
    (fun ω i => p.coordinate i (x ω)) (fun ω i => p.coordinate i (y ω))
    hxrep hyrep top bottom htop hbottom hindTop hindBottom (p.m s) ρ L hρ hL hI
    (horder.mono (fun _ h i hi => h (coord i hi)))
    hforceTop hforceBottom hprobTop hprobBottom
    (fun ω => p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω))
    (hr.mono (fun _ h => (h k).1))
  filter_upwards [hr] with ω hω
  intro i hi hcross
  have hc : L ≤ p.coordCost (coord i hi) := by
    change L ≤ p.C (s - 1 + 1)
    rwa [hs']
  exact ((hω k).2 (coord i hi) hcross).trans (Real.exp_le_exp.mpr (neg_le_neg hc))

theorem parameter_tail_conditional_attenuation
    {Ω : Type*} (mx my : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (hmx : mx ≤ mΩ) (hmy : my ≤ mΩ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (x y : Ω → Circle) (hx : Measurable[mx] x) (hy : Measurable[my] y)
    (hacx : μ.map x ≪ circleMeasure) (hacy : μ.map y ≪ circleMeasure)
    (horder : ∀ᵐ ω ∂μ, ∀ i : p.Coord,
      p.coordinate i.2 (x ω) ≤ p.coordinate i.2 (y ω))
    (top bottom : Bool → ℕ → Set Ω)
    (htop : ∀ which i, MeasurableSet (top which i))
    (hbottom : ∀ which i, MeasurableSet (bottom which i))
    (hindTop : ∀ which, iCondIndepSet mx hmx (top which) μ)
    (hindBottom : ∀ which, iCondIndepSet my hmy (bottom which) μ)
    (j : ℕ) (hj : 1 ≤ j)
    (hlabels : ∀ s, j ≤ s → ∀ which : Bool, ∀ i ∈ p.block s,
      ∀ u ∈ Icc (if which then p.b s else p.a s)
        (1 - (if which then p.b s else p.a s)), ∀ᵐ ω ∂μ,
        (p.coordinate i (x ω) < u → ω ∈ top which i → u ≤ p.coordinate i (y ω)) ∧
        (u ≤ p.coordinate i (y ω) → ω ∈ bottom which i → p.coordinate i (x ω) < u) ∧
        (p.coordinate i (x ω) < u →
          (kappa s * Real.sqrt ((if which then p.b s else p.a s) / (p.m s : ℝ))) / 10 ≤
            (μ[(top which i).indicator (fun _ => (1 : ℝ)) | mx]) ω) ∧
        (u ≤ p.coordinate i (y ω) →
          (kappa s * Real.sqrt ((if which then p.b s else p.a s) / (p.m s : ℝ))) / 10 ≤
            (μ[(bottom which i).indicator (fun _ => (1 : ℝ)) | my]) ω))
    (E : Set Ω) (htag : ∀ᵐ ω ∂μ, ω ∈ E → ∃ i ∈ p.block j,
      p.coordinate i (x ω) < 1 / (p.m j : ℝ) ∧
        1 - 1 / (p.m j : ℝ) < p.coordinate i (y ω))
    (k : ℤ) (hk : (p.K j : ℝ) < |(k : ℝ)|) :
    ∃ H₁ H₂ : Set Ω, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂μ, (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂μ, (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂μ, ω ∈ E →
        p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω) ≤
          Real.exp (-p.L j) + H₁.indicator (fun _ => (1 : ℝ)) ω +
            H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  by_cases hnear : |(k : ℝ)| ≤ p.N j / 4
  · exact CrossingAvoidance.empty_exceptional_events mx my μ E
      (fun ω => p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω))
      (Real.exp (-p.L j)) (Real.exp (-p.L j / 400)) (Real.exp_pos _).le
      (hp.ae_parameter_tagged_ratio_le_exp μ x y
        (hx.mono hmx le_rfl).aemeasurable (hy.mono hmy le_rfl).aemeasurable
        hacx hacy horder j hj k hk hnear E htag)
  · obtain ⟨s, w, I, hjs, hw, hIs, hI, hthreshold, hIntensity, hcost⟩ :=
      hp.exists_tail_crossing_set j hj k (le_of_not_ge hnear)
    obtain ⟨which, rfl⟩ : ∃ which : Bool, w = if which then p.b s else p.a s := by
      rcases hw with hw | ⟨_, hw⟩
      · exact ⟨true, by simpa using hw⟩
      · exact ⟨false, by simpa using hw⟩
    let w : ℝ := if which then p.b s else p.a s
    let ρ : ℝ := kappa s * Real.sqrt (w / (p.m s : ℝ))
    have hρ : 0 ≤ ρ := mul_nonneg (by unfold kappa; positivity) (Real.sqrt_nonneg _)
    have hl : ∀ᵐ ω ∂μ, ∀ i ∈ I,
        (p.coordinate i (x ω) < 1 - Int.fract ((k : ℝ) * p.alpha θ i) →
          ω ∈ top which i → 1 - Int.fract ((k : ℝ) * p.alpha θ i) ≤ p.coordinate i (y ω)) ∧
        (1 - Int.fract ((k : ℝ) * p.alpha θ i) ≤ p.coordinate i (y ω) →
          ω ∈ bottom which i → p.coordinate i (x ω) < 1 - Int.fract ((k : ℝ) * p.alpha θ i)) ∧
        (p.coordinate i (x ω) < 1 - Int.fract ((k : ℝ) * p.alpha θ i) →
          ρ / 10 ≤ (μ[(top which i).indicator (fun _ => (1 : ℝ)) | mx]) ω) ∧
        (1 - Int.fract ((k : ℝ) * p.alpha θ i) ≤ p.coordinate i (y ω) →
          ρ / 10 ≤ (μ[(bottom which i).indicator (fun _ => (1 : ℝ)) | my]) ω) := by
      apply ae_all_iff.mpr
      intro i
      apply ae_all_iff.mpr
      intro hi
      exact hlabels s hjs which i (hIs hi)
        (1 - Int.fract ((k : ℝ) * p.alpha θ i)) (hthreshold i hi)
    obtain ⟨H₁, H₂, hm₁, hm₂, hb₁, hb₂, hr⟩ :=
      hp.finite_parameter_conditional_attenuation mx my hmx hmy μ x y hx hy hacx hacy
        horder (top which) (bottom which) (htop which) (hbottom which)
        (hindTop which) (hindBottom which) s (hj.trans hjs) k I hIs hI
        ρ (p.L j) hρ hIntensity hcost
        (hl.mono (fun _ h i hi => (h i hi).1))
        (hl.mono (fun _ h i hi => (h i hi).2.1))
        (hl.mono (fun _ h i hi => (h i hi).2.2.1))
        (hl.mono (fun _ h i hi => (h i hi).2.2.2))
    exact ⟨H₁, H₂, hm₁, hm₂, hb₁, hb₂, hr.mono (fun _ h _ => h)⟩

end Invariant233.CircleParameterLaws

end

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

theorem ofDigits_nonneg {r : ℕ → ℕ} (d : Digits r) : 0 ≤ ofDigits d :=
  tsum_nonneg (term_nonneg d)

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

theorem tailValue_mem_bin {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) (j : ℕ) :
    (d j : ℝ) / (r j : ℝ) ≤ tailValue d j ∧
      tailValue d j ≤ ((d j : ℝ) + 1) / (r j : ℝ) := by
  rw [tailValue_rec hr d j]
  constructor
  · exact div_le_div_of_nonneg_right (by linarith [tailValue_nonneg d (j + 1)])
      (Nat.cast_nonneg _)
  · exact div_le_div_of_nonneg_right (by linarith [tailValue_le_one hr d (j + 1)])
      (Nat.cast_nonneg _)

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

theorem measurable_canonicalDigits (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) :
    Measurable (canonicalDigits r hr) := by
  apply Measurable.of_eval
  intro n
  exact (measurable_of_countable (fun k : ℕ =>
    (⟨k % r n, Nat.mod_lt _ (hr n)⟩ : Fin (r n)))).comp
      ((measurable_const.mul measurable_id).nat_floor)

theorem ofDigits_mem_Ico {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) : ofDigits d ∈ Set.Ico 0 1 := by
  refine ⟨ofDigits_nonneg d, ?_⟩
  simpa [tailValue, ofDigits] using tailValue_lt_one hr d hnt 0

theorem floor_denominator_mul_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) (N : ℕ) :
    ⌊(denominator r N : ℝ) * ofDigits d⌋₊ = prefixRank d N := by
  apply (Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) (ofDigits_nonneg d))).mpr
  rw [denominator_mul_ofDigits hr d N]
  constructor
  · linarith [tailValue_nonneg d N]
  · linarith [tailValue_lt_one hr d hnt N]

theorem canonicalDigits_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) : canonicalDigits r hr (ofDigits d) = d := by
  funext n
  have hrank := prefixRank_canonicalDigits hr (ofDigits_mem_Ico hr d hnt) (n + 1)
  rw [floor_denominator_mul_ofDigits hr d hnt (n + 1)] at hrank
  exact (prefixRank_eq_iff hr _ _ (n + 1)).mp hrank n (Nat.lt_succ_self n)

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

lemma coupling_bin_small {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s)
    {w : ℝ} (hw : 1 / (p.m s : ℝ) ≤ w) :
    1 / (MixedRadix.radices p.q i : ℝ) < w / 2 := by
  have hm : (0 : ℝ) < p.m s := by exact_mod_cast hp.m_pos s hs
  have hk : (100 : ℝ) ≤ p.K s := by exact_mod_cast hp.coupling_K_ge s hs
  have hN : (0 : ℝ) < p.N s := by unfold N; positivity
  have hmN : 2 * (p.m s : ℝ) < p.N s := by unfold N; nlinarith
  calc
    _ ≤ 1 / p.N s := one_div_le_one_div_of_le hN (hp.coupling_radix_ge_N hs hi)
    _ < (1 / (p.m s : ℝ)) / 2 := by
      rw [div_div]
      apply one_div_lt_one_div_of_lt (by positivity)
      linarith
    _ ≤ _ := div_le_div_of_nonneg_right hw (by norm_num)

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_IndependentCoordinateConditioning
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ProbabilityTheory Classical

namespace Invariant233.CoordinateConditioning

variable {ι : Type*} {X Y : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

theorem integral_finset_prod (S : Finset ι) (f : ∀ i, X i → ℝ)
    (hf : ∀ i, Measurable (f i)) :
    ∫ x, ∏ i ∈ S, f i (x i) ∂Measure.infinitePi μ =
      ∏ i ∈ S, ∫ x, f i x ∂μ i := by
  classical
  have he : (fun x : ∀ i, X i => ∏ i ∈ S, f i (x i)) =
      (fun z : ∀ i : S, X i => ∏ i : S, f i (z i)) ∘ S.restrict := by
    funext x
    simp only [Function.comp_apply, Finset.restrict]
    exact (S.prod_coe_sort (fun i => f i (x i))).symm
  rw [he]
  change (∫ x, (∏ i : S, f i (S.restrict x i)) ∂Measure.infinitePi μ) = _
  rw [MeasureTheory.integral_restrict_infinitePi μ (s := S)
    (f := fun z : ∀ i : S, X i => ∏ i : S, f i (z i))]
  · rw [integral_fintype_prod_eq_prod]
    exact S.prod_coe_sort (fun i => ∫ x, f i x ∂μ i)
  · exact (Finset.measurable_prod Finset.univ
      (fun (i : S) _ => (hf i).comp (measurable_pi_apply i))).aestronglyMeasurable

theorem integrable_finset_prod (S : Finset ι) (f : ∀ i, X i → ℝ)
    (hf : ∀ i, Measurable (f i)) (hb : ∀ i x, ‖f i x‖ ≤ 1) :
    Integrable (fun x : ∀ i, X i => ∏ i ∈ S, f i (x i)) (Measure.infinitePi μ) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact (Finset.measurable_prod S
      (fun i _ => (hf i).comp (measurable_pi_apply i))).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      rw [norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hb i (x i))

private theorem prod_extend (S T : Finset ι) (f : ι → ℝ) :
    ∏ i ∈ S ∪ T, (if i ∈ S then f i else 1) = ∏ i ∈ S, f i := by
  classical
  rw [Finset.prod_ite_mem]
  simp

omit [∀ i, MeasurableSpace (X i)] in

private theorem cylinder_indicator_prod (S T : Finset ι) (f : ∀ i, X i → ℝ)
    (B : ∀ i, Set (X i)) (x : ∀ i, X i) :
    ((T : Set ι).pi B).indicator (fun x => ∏ i ∈ S, f i (x i)) x =
      ∏ i ∈ S ∪ T,
        (if i ∈ T then (B i).indicator
          (fun z => if i ∈ S then f i z else 1) (x i)
         else if i ∈ S then f i (x i) else 1) := by
  classical
  by_cases hx : x ∈ (T : Set ι).pi B
  · rw [Set.indicator_of_mem hx]
    have hval : ∀ i ∈ S ∪ T,
        (if i ∈ T then (B i).indicator (fun z => if i ∈ S then f i z else 1) (x i)
          else if i ∈ S then f i (x i) else 1) = if i ∈ S then f i (x i) else 1 := by
      intro i hi
      by_cases hit : i ∈ T
      · rw [ite_eq_left hit, Set.indicator_of_mem (hx i hit)]
      · rw [ite_eq_right hit]
    rw [Finset.prod_congr rfl hval]
    exact (prod_extend S T (fun i => f i (x i))).symm
  · rw [Set.indicator_of_notMem hx]
    symm
    simp only [Set.mem_pi, Finset.mem_coe, not_forall] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    apply Finset.prod_eq_zero (Finset.mem_union_right S hi)
    rw [ite_eq_left hi, Set.indicator_of_notMem hxi]

theorem setIntegral_cylinder_prod_eq
    (S T : Finset ι) (A : ∀ i, X i → Y i)
    (hA : ∀ i, Measurable (A i))
    (f g : ∀ i, X i → ℝ) (hf : ∀ i, Measurable (f i))
    (hg : ∀ i, Measurable (g i))
    (hloc : ∀ i (B : Set (Y i)), MeasurableSet B →
      ∫ x in A i ⁻¹' B, g i x ∂μ i = ∫ x in A i ⁻¹' B, f i x ∂μ i)
    (B : ∀ i, Set (Y i)) (hB : ∀ i, MeasurableSet (B i)) :
    ∫ x in (fun x i => A i (x i)) ⁻¹' (T : Set ι).pi B,
        ∏ i ∈ S, g i (x i) ∂Measure.infinitePi μ =
      ∫ x in (fun x i => A i (x i)) ⁻¹' (T : Set ι).pi B,
        ∏ i ∈ S, f i (x i) ∂Measure.infinitePi μ := by
  classical
  have hp : (fun x i => A i (x i)) ⁻¹' (T : Set ι).pi B =
      (T : Set ι).pi (fun i => A i ⁻¹' B i) := rfl
  have hm : MeasurableSet ((T : Set ι).pi (fun i => A i ⁻¹' B i)) :=
    MeasurableSet.pi T.countable_toSet (fun i _ => hA i (hB i))
  rw [hp, ← integral_indicator hm, ← integral_indicator hm]
  simp_rw [cylinder_indicator_prod]
  let factors (F : ∀ i, X i → ℝ) : ∀ i, X i → ℝ := fun i z =>
    if i ∈ T then (A i ⁻¹' B i).indicator
      (fun z => if i ∈ S then F i z else 1) z
    else if i ∈ S then F i z else 1
  change (∫ x, ∏ i ∈ S ∪ T, factors g i (x i) ∂Measure.infinitePi μ) =
    (∫ x, ∏ i ∈ S ∪ T, factors f i (x i) ∂Measure.infinitePi μ)
  rw [integral_finset_prod μ (S ∪ T) (factors g),
    integral_finset_prod μ (S ∪ T) (factors f)]
  · apply Finset.prod_congr rfl
    intro i hi
    dsimp only [factors]
    by_cases hit : i ∈ T <;> by_cases his : i ∈ S
    · simp only [ite_eq_left hit, ite_eq_left his]
      rw [integral_indicator (hA i (hB i)), integral_indicator (hA i (hB i))]
      exact hloc i (B i) (hB i)
    · simp only [ite_eq_left hit, ite_eq_right his]
    · simp only [ite_eq_right hit, ite_eq_left his]
      simpa using hloc i Set.univ MeasurableSet.univ
    · simp only [ite_eq_right hit, ite_eq_right his]
  all_goals
    intro i
    have hset : MeasurableSet (A i ⁻¹' B i) := hA i (hB i)
    dsimp only [factors]
    split_ifs <;> fun_prop

theorem setIntegral_observed_prod_eq
    (S : Finset ι) (A : ∀ i, X i → Y i)
    (hA : ∀ i, Measurable (A i))
    (f g : ∀ i, X i → ℝ) (hf : ∀ i, Measurable (f i))
    (hg : ∀ i, Measurable (g i))
    (hfb : ∀ i x, ‖f i x‖ ≤ 1) (hgb : ∀ i x, ‖g i x‖ ≤ 1)
    (hloc : ∀ i (B : Set (Y i)), MeasurableSet B →
      ∫ x in A i ⁻¹' B, g i x ∂μ i = ∫ x in A i ⁻¹' B, f i x ∂μ i)
    (B : Set (∀ i, Y i)) (hB : MeasurableSet B) :
    ∫ x in (fun x i => A i (x i)) ⁻¹' B,
        ∏ i ∈ S, g i (x i) ∂Measure.infinitePi μ =
      ∫ x in (fun x i => A i (x i)) ⁻¹' B,
        ∏ i ∈ S, f i (x i) ∂Measure.infinitePi μ := by
  classical
  let obs : (∀ i, X i) → (∀ i, Y i) := fun x i => A i (x i)
  have hm : Measurable obs := Measurable.of_eval
    (fun i => (hA i).comp (measurable_pi_apply i))
  have hfi := integrable_finset_prod μ S f hf hfb
  have hgi := integrable_finset_prod μ S g hg hgb
  have htotal : (∫ x, ∏ i ∈ S, g i (x i) ∂Measure.infinitePi μ) =
      (∫ x, ∏ i ∈ S, f i (x i) ∂Measure.infinitePi μ) := by
    rw [integral_finset_prod μ S g hg, integral_finset_prod μ S f hf]
    apply Finset.prod_congr rfl
    intro i hi
    simpa using hloc i Set.univ MeasurableSet.univ
  refine MeasurableSpace.induction_on_inter
    (C := fun D _ =>
      (∫ x in obs ⁻¹' D, ∏ i ∈ S, g i (x i) ∂Measure.infinitePi μ) =
        (∫ x in obs ⁻¹' D, ∏ i ∈ S, f i (x i) ∂Measure.infinitePi μ))
    generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet)
      (fun _ => MeasurableSet.univ)) ?_ ?_ ?_ ?_ B hB
  · simp
  · rintro C ⟨T, D, hD, rfl⟩
    exact setIntegral_cylinder_prod_eq μ S T A hA f g hf hg hloc D
      (fun i => hD i (Set.mem_univ i))
  · intro C hC ih
    have heqg := integral_add_compl (hm hC) hgi
    have heqf := integral_add_compl (hm hC) hfi
    change (∫ x in obs ⁻¹' C, ∏ i ∈ S, g i (x i) ∂Measure.infinitePi μ) =
      (∫ x in obs ⁻¹' C, ∏ i ∈ S, f i (x i) ∂Measure.infinitePi μ) at ih
    rw [Set.preimage_compl]
    linarith
  · intro C hdisj hC ih
    rw [Set.preimage_iUnion,
      integral_iUnion (fun n => hm (hC n))
        (fun i j hij => (hdisj hij).preimage obs) hgi.integrableOn,
      integral_iUnion (fun n => hm (hC n))
        (fun i j hij => (hdisj hij).preimage obs) hfi.integrableOn]
    exact tsum_congr ih

theorem condExp_finset_prod
    (S : Finset ι) (A : ∀ i, X i → Y i)
    (hA : ∀ i, Measurable (A i))
    (f : ∀ i, X i → ℝ) (p : ∀ i, Y i → ℝ)
    (hf : ∀ i, Measurable (f i)) (hp : ∀ i, Measurable (p i))
    (hfb : ∀ i x, ‖f i x‖ ≤ 1) (hpb : ∀ i y, ‖p i y‖ ≤ 1)
    (hloc : ∀ i (B : Set (Y i)), MeasurableSet B →
      ∫ x in A i ⁻¹' B, p i (A i x) ∂μ i = ∫ x in A i ⁻¹' B, f i x ∂μ i) :
    (Measure.infinitePi μ)[(fun x => ∏ i ∈ S, f i (x i)) |
      MeasurableSpace.comap (fun x i => A i (x i)) inferInstance] =ᵐ[Measure.infinitePi μ]
      (fun x => ∏ i ∈ S, p i (A i (x i))) := by
  classical
  let obs : (∀ i, X i) → (∀ i, Y i) := fun x i => A i (x i)
  have hm : Measurable obs := Measurable.of_eval
    (fun i => (hA i).comp (measurable_pi_apply i))
  have hpA : ∀ i, Measurable (fun x => p i (A i x)) := fun i => (hp i).comp (hA i)
  have hpAb : ∀ i x, ‖p i (A i x)‖ ≤ 1 := fun i x => hpb i (A i x)
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm.comap_le
    (integrable_finset_prod μ S f hf hfb)
  · intro B hB hfin
    exact (integrable_finset_prod μ S _ hpA hpAb).integrableOn
  · intro B hB hfin
    obtain ⟨C, hC, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hB
    exact setIntegral_observed_prod_eq μ S A hA f _ hf hpA hfb hpAb hloc C hC
  · have hobs : @Measurable _ _ (MeasurableSpace.comap obs inferInstance) _ obs :=
      Measurable.of_comap_le le_rfl
    exact ((Finset.measurable_prod S (fun i _ =>
      (hp i).comp (measurable_pi_apply i))).comp hobs).aestronglyMeasurable

section Labels

variable {L : ι → Type*} [∀ i, MeasurableSpace (L i)]
  [∀ i, StandardBorelSpace (L i)] [∀ i, Nonempty (L i)]

theorem condExp_label_product
    (S : Finset ι) (A : ∀ i, X i → Y i) (hA : ∀ i, Measurable (A i))
    (label : ∀ i, X i → L i) (hl : ∀ i, Measurable (label i))
    (C : ∀ i, Set (L i)) (hC : ∀ i, MeasurableSet (C i)) :
    (Measure.infinitePi μ)[(fun x => ∏ i ∈ S,
      (label i ⁻¹' C i).indicator (fun _ => (1 : ℝ)) (x i)) |
      MeasurableSpace.comap (fun x i => A i (x i)) inferInstance] =ᵐ[Measure.infinitePi μ]
      (fun x => ∏ i ∈ S, (condDistrib (label i) (A i) (μ i) (A i (x i))).real (C i)) := by
  apply condExp_finset_prod μ S A hA
    (fun i => (label i ⁻¹' C i).indicator (fun _ => (1 : ℝ)))
    (fun i y => (condDistrib (label i) (A i) (μ i) y).real (C i))
  · intro i
    exact measurable_const.indicator (hl i (hC i))
  · intro i
    exact (Kernel.measurable_coe _ (hC i)).ennreal_toReal
  · intro i x
    by_cases hx : label i x ∈ C i <;> simp [Set.indicator, hx]
  · intro i y
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  · intro i B hB
    have he := condDistrib_ae_eq_condExp (μ := μ i) (hA i) (hl i) (hC i)
    calc
      (∫ x in A i ⁻¹' B, (condDistrib (label i) (A i) (μ i) (A i x)).real (C i) ∂μ i) =
          ∫ x in A i ⁻¹' B,
            (μ i)[(label i ⁻¹' C i).indicator (fun _ => (1 : ℝ)) |
              MeasurableSpace.comap (A i) inferInstance] x ∂μ i :=
        integral_congr_ae (ae_restrict_of_ae he)
      _ = _ := setIntegral_condExp (hA i).comap_le
        ((integrable_const (1 : ℝ)).indicator (hl i (hC i))) ⟨B, hB, rfl⟩

theorem condExp_label_inter
    (S : Finset ι) (A : ∀ i, X i → Y i) (hA : ∀ i, Measurable (A i))
    (label : ∀ i, X i → L i) (hl : ∀ i, Measurable (label i))
    (C : ∀ i, Set (L i)) (hC : ∀ i, MeasurableSet (C i)) :
    (Measure.infinitePi μ)⟦(⋂ i ∈ S, (fun x : ∀ i, X i => label i (x i)) ⁻¹' C i) |
      MeasurableSpace.comap (fun x i => A i (x i)) inferInstance⟧ =ᵐ[Measure.infinitePi μ]
      (fun x => ∏ i ∈ S, (condDistrib (label i) (A i) (μ i) (A i (x i))).real (C i)) := by
  have hind :
      (⋂ i ∈ S, (fun x : ∀ i, X i => label i (x i)) ⁻¹' C i).indicator
        (fun _ => (1 : ℝ)) =
      (fun x => ∏ i ∈ S, (label i ⁻¹' C i).indicator (fun _ => (1 : ℝ)) (x i)) := by
    funext x
    simpa [Set.indicator, Finset.prod_apply] using
      (prod_indicator_apply S
        (fun i => (fun x : ∀ i, X i => label i (x i)) ⁻¹' C i)
        (fun _ _ => (1 : ℝ)) x).symm
  change MeasureTheory.condExp _ (Measure.infinitePi μ) _ =ᵐ[Measure.infinitePi μ] _
  rw [hind]
  exact condExp_label_product μ S A hA label hl C hC

theorem iCondIndepFun_labels [Countable ι] [∀ i, StandardBorelSpace (X i)]
    (A : ∀ i, X i → Y i) (hA : ∀ i, Measurable (A i))
    (label : ∀ i, X i → L i) (hl : ∀ i, Measurable (label i)) :
    iCondIndepFun
      (MeasurableSpace.comap (fun x i => A i (x i)) inferInstance)
      (Measurable.of_eval (fun i => (hA i).comp (measurable_pi_apply i))).comap_le
      (fun i x => label i (x i)) (Measure.infinitePi μ) := by
  classical
  apply (iCondIndepFun_iff_condExp_inter_preimage_eq_mul
    (μ := Measure.infinitePi μ)
    (m' := MeasurableSpace.comap (fun x i => A i (x i)) inferInstance)
    (fun i => inferInstance) (fun i (x : ∀ i, X i) => label i (x i))
    (fun i => (hl i).comp (measurable_pi_apply i))).2
  intro S C hC
  let D : ∀ i, Set (L i) := fun i => if i ∈ S then C i else Set.univ
  have hD : ∀ i, MeasurableSet (D i) := by
    intro i
    by_cases hi : i ∈ S
    · simpa [D, hi] using hC i hi
    · simp [D, hi]
  have hDC : ∀ i ∈ S, D i = C i := fun i hi => ite_eq_left hi
  have hsets : (⋂ i ∈ S, (fun x : ∀ i, X i => label i (x i)) ⁻¹' C i) =
      (⋂ i ∈ S, (fun x : ∀ i, X i => label i (x i)) ⁻¹' D i) := by
    apply Set.iInter₂_congr
    intro i hi
    rw [hDC i hi]
  rw [hsets]
  have hjoint := condExp_label_inter μ S A hA label hl D hD
  have hsingle : ∀ i ∈ S,
      (Measure.infinitePi μ)⟦(fun x : ∀ i, X i => label i (x i)) ⁻¹' C i |
        MeasurableSpace.comap (fun x i => A i (x i)) inferInstance⟧ =ᵐ[Measure.infinitePi μ]
        (fun x => (condDistrib (label i) (A i) (μ i) (A i (x i))).real (D i)) := by
    intro i hi
    simpa [hDC i hi] using condExp_label_inter μ {i} A hA label hl D hD
  have hall := (ae_ball_iff S.countable_toSet).2 hsingle
  filter_upwards [hjoint, hall] with x hx hallx
  rw [Finset.prod_apply, hx]
  exact Finset.prod_congr rfl (fun i hi => (hallx i hi).symm)

theorem condExp_label_inter_of_disintegration
    (S : Finset ι) (A : ∀ i, X i → Y i) (hA : ∀ i, Measurable (A i))
    (label : ∀ i, X i → L i) (hl : ∀ i, Measurable (label i))
    (κ : ∀ i, Kernel (Y i) (L i)) [∀ i, IsFiniteKernel (κ i)]
    (hκ : ∀ i, (μ i).map (fun x => (A i x, label i x)) = (μ i).map (A i) ⊗ₘ κ i)
    (C : ∀ i, Set (L i)) (hC : ∀ i, MeasurableSet (C i)) :
    (Measure.infinitePi μ)⟦(⋂ i ∈ S, (fun x : ∀ i, X i => label i (x i)) ⁻¹' C i) |
      MeasurableSpace.comap (fun x i => A i (x i)) inferInstance⟧ =ᵐ[Measure.infinitePi μ]
      (fun x => ∏ i ∈ S, (κ i (A i (x i))).real (C i)) := by
  refine (condExp_label_inter μ S A hA label hl C hC).trans ?_
  have hlocal (i : ι) : ∀ᵐ x ∂μ i,
      condDistrib (label i) (A i) (μ i) (A i x) = κ i (A i x) :=
    ae_of_ae_map (hA i).aemeasurable
      (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (hA i) (hl i) (hκ i))
  have hglobal (i : ι) : ∀ᵐ x ∂Measure.infinitePi μ,
      condDistrib (label i) (A i) (μ i) (A i (x i)) = κ i (A i (x i)) :=
    (measurePreserving_eval_infinitePi μ i).quasiMeasurePreserving.ae (hlocal i)
  filter_upwards [(ae_ball_iff S.countable_toSet).2 (fun i _ => hglobal i)] with x hx
  exact Finset.prod_congr rfl (fun i hi => congrArg (fun ν => ν.real (C i)) (hx i hi))

end Labels

end Invariant233.CoordinateConditioning

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CouplingMixture
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

lemma bin_subset_top_left {r : ℕ} [NeZero r] (d : Fin r)
    {z u w : ℝ} (hz : z ∈ bin r d) (hzu : z < u) (hu : u ≤ 1 - w)
    (hsmall : 1 / (r : ℝ) < w / 2) :
    bin r d ⊆ Ico (0 : ℝ) (1 - w / 2) := by
  intro x hx
  have hx0 := (bin_subset_unit d hx).1
  have hlen := bin_length d
  exact ⟨hx0, by dsimp [bin] at hz hx <;> linarith [hz.1, hx.2]⟩

lemma bin_subset_bottom_right {r : ℕ} [NeZero r] (d : Fin r)
    {z u w : ℝ} (hz : z ∈ bin r d) (hzu : u ≤ z) (hu : w ≤ u)
    (hsmall : 1 / (r : ℝ) < w / 2) :
    bin r d ⊆ Ico (w / 2) (1 : ℝ) := by
  intro x hx
  have hx1 := (bin_subset_unit d hx).2
  have hlen := bin_length d
  exact ⟨by dsimp [bin] at hz hx <;> linarith [hz.2, hx.1], hx1⟩

lemma abs_sub_lt_bin_width {r : ℕ} (d : Fin r) {x y : ℝ}
    (hx : x ∈ bin r d) (hy : y ∈ bin r d) :
    |x - y| < 1 / (r : ℝ) := by
  rw [abs_lt]
  have hlen := bin_length d
  constructor <;> dsimp [bin] at hx hy <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma top_forces_crossing {r : ℕ} {Y y u w : ℝ}
    (hY : 1 - w / 2 ≤ Y) (hround : |y - Y| ≤ 1 / (r : ℝ))
    (hsmall : 1 / (r : ℝ) < w / 2) (hu : u ≤ 1 - w) : u ≤ y := by
  have h := (abs_le.mp hround).1
  linarith

lemma bottom_forces_crossing {r : ℕ} {X x u w : ℝ}
    (hX : X < w / 2) (hround : |x - X| ≤ 1 / (r : ℝ))
    (hsmall : 1 / (r : ℝ) < w / 2) (hu : w ≤ u) : x < u := by
  have h := (abs_le.mp hround).2
  linarith

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleDigitCoupling
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

lemma labelsGivenDigit_singleton (side : Bool) (r : ℕ) (κ m a b t : ℝ)
    (d : Fin r) (l : Label) :
    labelsGivenDigit side r κ m a b t d {l} =
      digitWeight side r κ m a b t l d / ∑ k, digitWeight side r κ m a b t k d := by
  classical
  cases l <;> simp [labelsGivenDigit, FiniteKernelMixture.normalizedKernel_apply,
    Kernel.const_apply, Pi.single_apply]

variable {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)

include hm ha ha' hb hb' in
lemma endpointLaw_isProbabilityMeasure (side : Bool) (l : Label) :
    IsProbabilityMeasure (endpointLaw side m a b l) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  cases l with
  | none => exact baseLaw_isProbabilityMeasure
  | some i =>
    cases side
    · exact leftLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb' i
    · exact rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb' i

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma digitWeight_total_ne_zero (side : Bool) (r : ℕ) [NeZero r] (d : Fin r) :
    (∑ l, digitWeight side r κ m a b t l d) ≠ 0 := by
  have hq : 0 < diagonalMass κ m a b t := by
    have := (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
    linarith
  have hpos : digitWeight side r κ m a b t none d ≠ 0 := by
    simp only [digitWeight, labelMass, endpointLaw, baseLaw_bin]
    exact mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hq)
      (ENNReal.inv_ne_zero.mpr (by simp))
  intro h
  apply hpos
  exact (Finset.sum_eq_zero_iff.mp h) none (Finset.mem_univ none)

include hm ha ha' hb hb' in
lemma digitWeight_total_ne_top (side : Bool) (r : ℕ) (d : Fin r) :
    (∑ l, digitWeight side r κ m a b t l d) ≠ ∞ := by
  have : ∀ l, IsProbabilityMeasure (endpointLaw side m a b l) :=
    endpointLaw_isProbabilityMeasure hm ha ha' hb hb' side
  apply ENNReal.sum_ne_top.mpr
  intro l _
  apply ENNReal.mul_ne_top
  · cases l <;> exact ENNReal.ofReal_ne_top
  · exact measure_ne_top _ _

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma labelsGivenDigit_isMarkov (side : Bool) (r : ℕ) [NeZero r] :
    IsMarkovKernel (labelsGivenDigit side r κ m a b t) := by
  apply FiniteKernelMixture.normalizedKernel_isMarkov
  · exact digitWeight_total_ne_zero hκ0 hκ hm ha ha' hb hb' ht0 ht side r
  · exact digitWeight_total_ne_top hm ha ha' hb hb' side r

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

lemma digitJoint_singleton (side : Bool) (r : ℕ) [NeZero r]
    (d : Fin r) (l : Label) :
    digitJoint side r κ m a b t {(d, l)} = digitWeight side r κ m a b t l d := by
  rw [digitJoint_eq_sum hm ha ha' hb hb']
  have hs : ({(d, l)} : Set (Fin r × Label)) = {d} ×ˢ {l} := by ext z; simp
  rw [hs]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Measure.prod_prod,
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  classical
  simp only [Set.mem_singleton_iff, mul_ite, mul_zero, Set.indicator_apply]
  rw [Finset.sum_eq_single l]
  · rw [endpointLaw_quantize_singleton hm ha ha' hb hb']
    simp [digitWeight]
  · intro k _ hkl
    simp [hkl]
  · simp

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

variable (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (ht0 : 0 ≤ t) (ht : t ≤ 1)
include hκ0 hκ ht0 ht

lemma labelsGivenDigit_disintegration (side : Bool) (r : ℕ) [NeZero r] :
    (digitJoint side r κ m a b t).fst ⊗ₘ labelsGivenDigit side r κ m a b t =
      digitJoint side r κ m a b t := by
  have := rawLaw_isProbabilityMeasure hκ0 hκ hm ha ha' hb hb' ht0 ht
  have : IsFiniteMeasure (digitJoint side r κ m a b t) := by
    unfold digitJoint
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have := labelsGivenDigit_isMarkov hκ0 hκ hm ha ha' hb hb' ht0 ht side r
  apply Measure.ext_of_singleton
  rintro ⟨d, l⟩
  have hs : ({(d, l)} : Set (Fin r × Label)) = {d} ×ˢ {l} := by ext z; simp
  rw [hs, Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    lintegral_singleton]
  rw [labelsGivenDigit_singleton, digitJoint_fst_singleton hm ha ha' hb hb', ← hs,
    digitJoint_singleton hm ha ha' hb hb']
  exact ENNReal.div_mul_cancel
    (digitWeight_total_ne_zero hκ0 hκ hm ha ha' hb hb' ht0 ht side r d)
    (digitWeight_total_ne_top hm ha ha' hb hb' side r d)

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleDigitCrossings
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

lemma baseLaw_le_intervalLaw_of_subset {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    {s : Set ℝ} (hs : s ⊆ Ico a b) : baseLaw s ≤ intervalLaw a b s := by
  rw [intervalLaw_eq_base_cond ha hb, ProbabilityTheory.cond_apply measurableSet_Ico,
    inter_eq_right.mpr hs]
  have hmass : baseLaw (Ico a b) ≤ 1 := by
    simpa using (measure_mono (subset_univ (Ico a b)) : baseLaw (Ico a b) ≤ baseLaw univ)
  simpa only [one_mul, mul_one, mul_comm] using
    mul_le_mul_right (ENNReal.one_le_inv.mpr hmass) (baseLaw s)

variable {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)
include hκ0 hκ hm ha ha' hb hb' ht0 ht

lemma label_posterior_lower_of_bin (side : Bool) (r : ℕ) [NeZero r]
    (d : Fin r) (l : Label)
    (hbin : baseLaw (bin r d) ≤ endpointLaw side m a b l (bin r d)) :
    labelMass κ m a b t l / 10 ≤ labelsGivenDigit side r κ m a b t d {l} := by
  rw [labelsGivenDigit_singleton]
  have h0 : baseLaw (bin r d) ≠ 0 := by rw [baseLaw_bin]; simp
  have hfin : baseLaw (bin r d) ≠ ∞ := measure_ne_top _ _
  calc
    _ = (labelMass κ m a b t l * baseLaw (bin r d)) /
      (10 * baseLaw (bin r d)) := (ENNReal.mul_div_mul_right _ _ h0 hfin).symm
    _ ≤ _ := ENNReal.div_le_div (mul_le_mul_right hbin _)
      (digitWeight_total_le_ten hκ0 hκ hm ha ha' hb hb' ht0 ht side r d)

lemma top_posterior_lower (r : ℕ) [NeZero r] (d : Fin r) (which : Bool)
    {z u : ℝ} (hz : z ∈ bin r d) (hzu : z < u)
    (hu : u ≤ 1 - width a b which) (hsmall : 1 / (r : ℝ) < width a b which / 2) :
    ENNReal.ofReal (rho κ m (width a b which)) / 10 ≤
      labelsGivenDigit false r κ m a b t d {topLabel which} := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hsubset := bin_subset_top_left d hz hzu hu hsmall
  have hlike : baseLaw (bin r d) ≤ endpointLaw false m a b (topLabel which) (bin r d) := by
    cases which <;> simp only [topLabel, endpointLaw, Bool.false_eq_true, ite_false, if_false,
      ite_true, if_true, leftLaw] <;> simp only [width, Bool.false_eq_true, ite_false, if_false, ite_true, if_true] at hsubset <;> apply baseLaw_le_intervalLaw_of_subset
    all_goals solve | norm_num | linarith | exact hsubset
  have hpost := label_posterior_lower_of_bin hκ0 hκ hm ha ha' hb hb' ht0 ht false r d (topLabel which) hlike
  cases which <;> simpa [labelMass, topLabel, componentProbabilities, width] using hpost

lemma bottom_posterior_lower (r : ℕ) [NeZero r] (d : Fin r) (which : Bool)
    {z u : ℝ} (hz : z ∈ bin r d) (hzu : u ≤ z)
    (hu : width a b which ≤ u) (hsmall : 1 / (r : ℝ) < width a b which / 2) :
    ENNReal.ofReal (rho κ m (width a b which)) / 10 ≤
      labelsGivenDigit true r κ m a b t d {bottomLabel which} := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hsubset := bin_subset_bottom_right d hz hzu hu hsmall
  have hlike : baseLaw (bin r d) ≤ endpointLaw true m a b (bottomLabel which) (bin r d) := by
    cases which <;> simp only [bottomLabel, endpointLaw, Bool.false_eq_true, ite_false, if_false,
      ite_true, if_true, rightLaw] <;> simp only [width, Bool.false_eq_true, ite_false, if_false, ite_true, if_true] at hsubset <;> apply baseLaw_le_intervalLaw_of_subset
    all_goals solve | norm_num | linarith | exact hsubset
  have hpost := label_posterior_lower_of_bin hκ0 hκ hm ha ha' hb hb' ht0 ht true r d (bottomLabel which) hlike
  cases which <;> simpa [labelMass, bottomLabel, componentProbabilities, width] using hpost

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingLaw
attribute [-instance] _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

omit hp in
lemma measurable_label (i : ℕ) : Measurable (label i) := by
  exact measurable_fst.comp (measurable_pi_apply i)

lemma iCondIndepFun_labels_digits (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    letI := law_isProbabilityMeasure hp j
    iCondIndepFun (MeasurableSpace.comap (digits p hr side) inferInstance)
      (measurable_digits hr side).comap_le label (law p j) := by
  let := coordinateLaw_isProbabilityMeasure hp j
  let := law_isProbabilityMeasure hp j
  exact CoordinateConditioning.iCondIndepFun_labels (coordinateLaw p j)
    (observedDigit p hr side) (measurable_observedDigit hr side)
    (fun _ => Prod.fst) (fun _ => measurable_fst)

lemma posterior_isMarkov (j : ℕ) (side : Bool) (i : ℕ) :
    IsMarkovKernel (posterior p j side i) := by
  by_cases hi : i = 0
  · simp only [posterior, ite_eq_left hi]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
  have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
    exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by have := hp.m_ge_200 _ hs; omega)
  let : NeZero (MixedRadix.radices p.q i) :=
    ⟨Nat.ne_of_gt (MixedRadix.radices_pos hp.q_pos hp.frequency_increasing hp.frequency_divisible i)⟩
  simpa only [posterior, ite_eq_right hi] using labelsGivenDigit_isMarkov
    (CircleParameterLaws.coupling_kappa_bounds _ hs).1
    (CircleParameterLaws.coupling_kappa_bounds _ hs).2 hm
    (hp.coupling_a_bounds _ hs).1 (hp.coupling_a_bounds _ hs).2
    (hp.coupling_b_bounds _ hs).1 (hp.coupling_b_bounds _ hs).2
    (tag_bounds j _).1 (tag_bounds j _).2 side (MixedRadix.radices p.q i)

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingDisintegration
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

lemma initial_disintegration {D : Type*} [MeasurableSpace D]
    (f : CoordinateSample → D) (hf : Measurable f) :
    (initialLaw.map f) ⊗ₘ Kernel.const D (Measure.dirac (none : Label)) =
      initialLaw.map (fun z => (f z, z.1)) := by
  let := initialLaw_isProbabilityMeasure
  rw [Measure.compProd_const, Measure.prod_dirac,
    Measure.map_map (show Measurable (fun d : D => (d, (none : Label))) from by fun_prop) hf]
  simp only [Function.comp_def]
  unfold initialLaw
  have hin : Measurable (fun x : ℝ => ((none : Label), (x, x))) := by fun_prop
  rw [Measure.map_map (show Measurable (fun z : CoordinateSample => (f z, (none : Label))) from by fun_prop) hin,
    Measure.map_map (show Measurable (fun z : CoordinateSample => (f z, z.1)) from by fun_prop) hin]
  rfl

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma posterior_disintegration (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ) :
    ((coordinateLaw p j i).map (observedDigit p hr side i)) ⊗ₘ posterior p j side i =
      (coordinateLaw p j i).map (fun z => (observedDigit p hr side i z, z.1)) := by
  by_cases hi : i = 0
  · simpa only [coordinateLaw, posterior, ite_eq_left hi] using
      initial_disintegration (observedDigit p hr side i) (measurable_observedDigit hr side i)
  have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
  have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
    exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by have := hp.m_ge_200 _ hs; omega)
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  have hd := labelsGivenDigit_disintegration hm
    (hp.coupling_a_bounds _ hs).1 (hp.coupling_a_bounds _ hs).2
    (hp.coupling_b_bounds _ hs).1 (hp.coupling_b_bounds _ hs).2
    (CircleParameterLaws.coupling_kappa_bounds _ hs).1
    (CircleParameterLaws.coupling_kappa_bounds _ hs).2
    (tag_bounds j (p.blockIndex i)).1 (tag_bounds j (p.blockIndex i)).2 side (MixedRadix.radices p.q i)
  have ho : observedDigit p hr side i = (fun z =>
      UniformQuantization.quantize (MixedRadix.radices p.q i) (endpoint side z)) := rfl
  rw [digitJoint,
    Measure.fst_map_prodMk measurable_fst] at hd
  simpa only [coordinateLaw, posterior, ite_eq_right hi, ho, digitJoint] using hd

end Invariant233.CircleCoupling

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
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ConditionalObservationTransport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory

namespace Invariant233.ConditionalObservationTransport

variable {Ω D Y E : Type*} [mΩ : MeasurableSpace Ω]
  [mD : MeasurableSpace D] [mY : MeasurableSpace Y]
  {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in

theorem aestronglyMeasurable_encoding
    [NormedAddCommGroup E] [CompleteSpace E]
    {X : Ω → D} {encode : D → Y} {decode : Y → D}
    (hdecode : Measurable decode)
    (hrecover : ∀ᵐ ω ∂μ, decode (encode (X ω)) = X ω)
    {g : Ω → E} (hg : StronglyMeasurable[mD.comap X] g) :
    AEStronglyMeasurable[mY.comap (encode ∘ X)] g μ := by
  obtain ⟨k, hk, hkg⟩ := hg.exists_eq_measurable_comp
  have hobs : Measurable[mY.comap (encode ∘ X)] (encode ∘ X) :=
    measurable_iff_comap_le.mpr le_rfl
  refine ⟨k ∘ decode ∘ (encode ∘ X),
    hk.comp_measurable (hdecode.comp hobs), ?_⟩
  filter_upwards [hrecover] with ω hω
  simp only [hkg, Function.comp_apply, hω]

theorem condExp_encoding
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {X : Ω → D} {encode : D → Y} {decode : Y → D}
    (hX : Measurable X) (hencode : Measurable encode) (hdecode : Measurable decode)
    (hrecover : ∀ᵐ ω ∂μ, decode (encode (X ω)) = X ω) (f : Ω → E) :
    μ[f | mY.comap (encode ∘ X)] =ᵐ[μ] μ[f | mD.comap X] := by
  have hle : mY.comap (encode ∘ X) ≤ mD.comap X := by
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hencode.comap_le
  have hsmall : mY.comap (encode ∘ X) ≤ mΩ := (hencode.comp hX).comap_le
  have hg : AEStronglyMeasurable[mY.comap (encode ∘ X)] (μ[f | mD.comap X]) μ :=
    aestronglyMeasurable_encoding hdecode hrecover stronglyMeasurable_condExp
  exact (condExp_condExp_of_le hle hX.comap_le).symm.trans
    (condExp_of_aestronglyMeasurable' hsmall hg integrable_condExp)

theorem iCondIndepFun_encoding_iff
    [StandardBorelSpace Ω] {ι : Type*} {β : ι → Type*}
    [mβ : ∀ i, MeasurableSpace (β i)]
    {X : Ω → D} {encode : D → Y} {decode : Y → D}
    (hX : Measurable X) (hencode : Measurable encode) (hdecode : Measurable decode)
    (hrecover : ∀ᵐ ω ∂μ, decode (encode (X ω)) = X ω)
    (L : ∀ i, Ω → β i) (hL : ∀ i, Measurable (L i)) :
    iCondIndepFun (mY.comap (encode ∘ X)) (hencode.comp hX).comap_le L μ ↔
      iCondIndepFun (mD.comap X) hX.comap_le L μ := by
  classical
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul mβ L hL,
    iCondIndepFun_iff_condExp_inter_preimage_eq_mul mβ L hL]
  have hce (s : Set Ω) :
      μ⟦s | mY.comap (encode ∘ X)⟧ =ᵐ[μ] μ⟦s | mD.comap X⟧ :=
    condExp_encoding hX hencode hdecode hrecover (s.indicator (fun _ => (1 : ℝ)))
  constructor
  · intro h S sets hsets
    have hp : (∏ i ∈ S, μ⟦L i ⁻¹' sets i | mY.comap (encode ∘ X)⟧) =ᵐ[μ]
        ∏ i ∈ S, μ⟦L i ⁻¹' sets i | mD.comap X⟧ :=
      eventuallyEq_prod (fun i _ => hce (L i ⁻¹' sets i))
    exact (hce _).symm.trans ((h S hsets).trans hp)
  · intro h S sets hsets
    have hp : (∏ i ∈ S, μ⟦L i ⁻¹' sets i | mY.comap (encode ∘ X)⟧) =ᵐ[μ]
        ∏ i ∈ S, μ⟦L i ⁻¹' sets i | mD.comap X⟧ :=
      eventuallyEq_prod (fun i _ => hce (L i ⁻¹' sets i))
    exact (hce _).trans ((h S hsets).trans hp.symm)

end Invariant233.ConditionalObservationTransport

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixTransport
attribute [-instance] _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.MixedRadix.hybrid_apply_ge _root_.OAI.Invariant233.MixedRadix.hybrid_apply_lt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.MixedRadix

theorem measurable_circleCanonical (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) :
    Measurable (circleCanonical r hr) :=
  (measurable_canonicalDigits r hr).comp
    (measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable)

theorem circleCanonical_circleValue {r : ℕ → ℕ} (hp : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) :
    circleCanonical r hp (circleValue d) = d := by
  have hx : ofDigits d ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    simpa using ofDigits_mem_Ico hp d hnt
  unfold circleCanonical circleValue
  rw [AddCircle.equivIco_coe_eq hx]
  exact canonicalDigits_ofDigits hp d hnt

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingConditioning
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators ProbabilityTheory
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma ae_recover_digits (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    ∀ᵐ ω ∂law p j, MixedRadix.circleCanonical (MixedRadix.radices p.q) hr
      (point p hr side ω) = digits p hr side ω := by
  filter_upwards [ae_nonterminal_digits hp j hr side] with ω hω
  exact MixedRadix.circleCanonical_circleValue hr _ hω

lemma iCondIndepFun_labels_point (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    letI := law_isProbabilityMeasure hp j
    iCondIndepFun (MeasurableSpace.comap (point p hr side) inferInstance)
      (measurable_point hp hr side).comap_le label (law p j) := by
  let := law_isProbabilityMeasure hp j
  exact (ConditionalObservationTransport.iCondIndepFun_encoding_iff
    (measurable_digits hr side)
    (MixedRadix.measurable_circleValue
      (MixedRadix.radices_ge_two hp.q_pos hp.frequency_increasing hp.frequency_divisible))
    (MixedRadix.measurable_circleCanonical _ hr) (ae_recover_digits hp j hr side)
    label measurable_label).2 (iCondIndepFun_labels_digits hp j hr side)

lemma condExp_labels_digits (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool)
    (S : Finset ℕ) (C : ℕ → Set Label) (hC : ∀ i, MeasurableSet (C i)) :
    (law p j)⟦(⋂ i ∈ S, label i ⁻¹' C i) |
      MeasurableSpace.comap (digits p hr side) inferInstance⟧ =ᵐ[law p j]
      (fun ω => ∏ i ∈ S, (posterior p j side i (digits p hr side ω i)).real (C i)) := by
  let := coordinateLaw_isProbabilityMeasure hp j
  let := posterior_isMarkov hp j side
  exact CoordinateConditioning.condExp_label_inter_of_disintegration (coordinateLaw p j)
    S (observedDigit p hr side) (measurable_observedDigit hr side)
    (fun _ => Prod.fst) (fun _ => measurable_fst) (posterior p j side)
    (fun i => (posterior_disintegration hp j hr side i).symm) C hC

lemma condExp_labels_point (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool)
    (S : Finset ℕ) (C : ℕ → Set Label) (hC : ∀ i, MeasurableSet (C i)) :
    (law p j)⟦(⋂ i ∈ S, label i ⁻¹' C i) |
      MeasurableSpace.comap (point p hr side) inferInstance⟧ =ᵐ[law p j]
      (fun ω => ∏ i ∈ S, (posterior p j side i
        (MixedRadix.circleCanonical (MixedRadix.radices p.q) hr (point p hr side ω) i)).real (C i)) := by
  let := law_isProbabilityMeasure hp j
  have he := ConditionalObservationTransport.condExp_encoding
    (measurable_digits hr side)
    (MixedRadix.measurable_circleValue
      (MixedRadix.radices_ge_two hp.q_pos hp.frequency_increasing hp.frequency_divisible))
    (MixedRadix.measurable_circleCanonical _ hr) (ae_recover_digits hp j hr side)
    ((⋂ i ∈ S, label i ⁻¹' C i).indicator (fun _ => (1 : ℝ)))
  refine he.trans ((condExp_labels_digits hp j hr side S C hC).trans ?_)
  filter_upwards [ae_recover_digits hp j hr side] with ω hω
  rw [hω]

lemma condExp_single_label_point (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ) (l : Label) :
    (law p j)⟦label i ⁻¹' {l} | MeasurableSpace.comap (point p hr side) inferInstance⟧ =ᵐ[law p j]
      (fun ω => (posterior p j side i
        (MixedRadix.circleCanonical (MixedRadix.radices p.q) hr (point p hr side ω) i)).real {l}) := by
  simpa using condExp_labels_point hp j hr side {i} (fun _ => {l})
    (fun _ => measurableSet_singleton l)

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingCrossings
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

lemma coordinate_point_mem_bin (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (side : Bool) (ω : Sample) (hnt : MixedRadix.Nonterminal (digits p hr side ω)) (i : ℕ) :
    p.coordinate i (point p hr side ω) ∈ bin (MixedRadix.radices p.q i) (digits p hr side ω i) := by
  rw [coordinate_point_eq_tail hp hr side ω hnt i]
  have h0 := (MixedRadix.tailValue_mem_bin hr (digits p hr side ω) i).1
  refine ⟨h0, ?_⟩
  change MixedRadix.tailValue (digits p hr side ω) i < _
  rw [MixedRadix.tailValue_rec hr]
  apply div_lt_div_of_pos_right _ (by exact_mod_cast hr i)
  linarith [MixedRadix.tailValue_lt_one hr (digits p hr side ω) hnt (i + 1)]

lemma ae_top_posterior_lower (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) (which : Bool) :
    ∀ᵐ ω ∂law p j, ∀ u : ℝ,
      p.coordinate i (point p hr false ω) < u → u ≤ 1 - width (p.a s) (p.b s) which →
      ENNReal.ofReal (CouplingMarginalBounds.rho (kappa s) (p.m s) (width (p.a s) (p.b s) which)) / 10 ≤
        posterior p j false i
          (MixedRadix.circleCanonical (MixedRadix.radices p.q) hr (point p hr false ω) i)
          {topLabel which} := by
  have hi0 : i ≠ 0 := by have := (p.mem_block_iff s i).mp hi; omega
  have hidx := p.blockIndex_eq_of_mem hp.m_pos hi
  have hm : (100 : ℝ) ≤ p.m s := by exact_mod_cast (show 100 ≤ p.m s by have := hp.m_ge_200 s hs; omega)
  have ha := hp.coupling_a_bounds s hs
  have hb := hp.coupling_b_bounds s hs
  have hκ := CircleParameterLaws.coupling_kappa_bounds s hs
  have hw : 1 / (p.m s : ℝ) ≤ width (p.a s) (p.b s) which := by
    cases which
    · exact ha.1
    · exact hb.1
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  filter_upwards [ae_nonterminal_digits hp j hr false, ae_recover_digits hp j hr false] with ω hnt hrec
  intro u hxu hu
  rw [hrec, posterior, ite_eq_right hi0, hidx]
  exact top_posterior_lower hκ.1 hκ.2 hm ha.1 ha.2 hb.1 hb.2
    (tag_bounds j s).1 (tag_bounds j s).2 _ _ which
    (coordinate_point_mem_bin hp hr false ω hnt i) hxu hu (hp.coupling_bin_small hs hi hw)

lemma ae_bottom_posterior_lower (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) (which : Bool) :
    ∀ᵐ ω ∂law p j, ∀ u : ℝ,
      u ≤ p.coordinate i (point p hr true ω) → width (p.a s) (p.b s) which ≤ u →
      ENNReal.ofReal (CouplingMarginalBounds.rho (kappa s) (p.m s) (width (p.a s) (p.b s) which)) / 10 ≤
        posterior p j true i
          (MixedRadix.circleCanonical (MixedRadix.radices p.q) hr (point p hr true ω) i)
          {bottomLabel which} := by
  have hi0 : i ≠ 0 := by have := (p.mem_block_iff s i).mp hi; omega
  have hidx := p.blockIndex_eq_of_mem hp.m_pos hi
  have hm : (100 : ℝ) ≤ p.m s := by exact_mod_cast (show 100 ≤ p.m s by have := hp.m_ge_200 s hs; omega)
  have ha := hp.coupling_a_bounds s hs
  have hb := hp.coupling_b_bounds s hs
  have hκ := CircleParameterLaws.coupling_kappa_bounds s hs
  have hw : 1 / (p.m s : ℝ) ≤ width (p.a s) (p.b s) which := by
    cases which
    · exact ha.1
    · exact hb.1
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  filter_upwards [ae_nonterminal_digits hp j hr true, ae_recover_digits hp j hr true] with ω hnt hrec
  intro u huy hu
  rw [hrec, posterior, ite_eq_right hi0, hidx]
  exact bottom_posterior_lower hκ.1 hκ.2 hm ha.1 ha.2 hb.1 hb.2
    (tag_bounds j s).1 (tag_bounds j s).2 _ _ which
    (coordinate_point_mem_bin hp hr true ω hnt i) huy hu (hp.coupling_bin_small hs hi hw)

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

lemma rawLaw_ae_top_support (which : Bool) :
    ∀ᵐ z ∂rawLaw κ m a b t, z.1 = topLabel which → 1 - width a b which / 2 ≤ z.2.2 := by
  apply rawLaw_ae_endpoint_property hm ha ha' hb hb' true (P := fun l x => l = topLabel which → 1 - width a b which / 2 ≤ x)
  · simp only [imp_iff_not_or, endpoint, ite_true, if_true]
    exact (measurableSet_eq_fun measurable_fst measurable_const).compl.union
      (measurableSet_le measurable_const (measurable_snd.comp measurable_snd))
  · exact Eventually.of_forall (by intro x h; cases which <;> cases h)
  · intro i
    by_cases hi : some i = topLabel which
    · cases which
      · have he : i = 0 := Option.some.inj hi
        subst i
        filter_upwards [intervalLaw_ae_mem (1 - a / 2) 1] with x hx
        exact fun _ => hx.1
      · have he : i = 2 := Option.some.inj hi
        subst i
        filter_upwards [intervalLaw_ae_mem (1 - b / 2) 1] with x hx
        exact fun _ => hx.1
    · exact Eventually.of_forall (fun _ h => (hi h).elim)

lemma rawLaw_ae_bottom_support (which : Bool) :
    ∀ᵐ z ∂rawLaw κ m a b t, z.1 = bottomLabel which → z.2.1 < width a b which / 2 := by
  apply rawLaw_ae_endpoint_property hm ha ha' hb hb' false (P := fun l x => l = bottomLabel which → x < width a b which / 2)
  · simp only [imp_iff_not_or, endpoint, Bool.false_eq_true, ite_false, if_false]
    exact (measurableSet_eq_fun measurable_fst measurable_const).compl.union
      (measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const)
  · exact Eventually.of_forall (by intro x h; cases which <;> cases h)
  · intro i
    by_cases hi : some i = bottomLabel which
    · cases which
      · have he : i = 1 := Option.some.inj hi
        subst i
        filter_upwards [intervalLaw_ae_mem 0 (a / 2)] with x hx
        exact fun _ => hx.2
      · have he : i = 3 := Option.some.inj hi
        subst i
        filter_upwards [intervalLaw_ae_mem 0 (b / 2)] with x hx
        exact fun _ => hx.2
    · exact Eventually.of_forall (fun _ h => (hi h).elim)

end Parameters
end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingForcing
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

lemma ae_endpoint_unit (j : ℕ) (i : ℕ) (side : Bool) :
    ∀ᵐ ω ∂law p j, endpoint side (ω i) ∈ Ico (0 : ℝ) 1 := by
  let := coordinateLaw_isProbabilityMeasure hp j
  apply (measurePreserving_eval_infinitePi (coordinateLaw p j) i).quasiMeasurePreserving.ae
    (p := fun z => endpoint side z ∈ Ico (0 : ℝ) 1)
  by_cases hi : i = 0
  · rw [coordinateLaw, ite_eq_left hi, initialLaw]
    apply (ae_map_iff (show Measurable (fun x : ℝ => ((none : Label), (x, x))) from by fun_prop).aemeasurable
      (show MeasurableSet {z : CoordinateSample | endpoint side z ∈ Ico (0 : ℝ) 1} from by
        apply measurableSet_Ico.preimage
        cases side
        · exact measurable_fst.comp measurable_snd
        · exact measurable_snd.comp measurable_snd)).2
    cases side <;> exact CouplingMixture.intervalLaw_ae_mem 0 1
  · have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
    have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by exact_mod_cast
      (show 100 ≤ p.m (p.blockIndex i) by have := hp.m_ge_200 _ hs; omega)
    rw [coordinateLaw, ite_eq_right hi]
    exact rawLaw_ae_endpoint_unit hm (hp.coupling_a_bounds _ hs).1 (hp.coupling_a_bounds _ hs).2
      (hp.coupling_b_bounds _ hs).1 (hp.coupling_b_bounds _ hs).2 side

lemma ae_rounding_bound (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (i : ℕ) (side : Bool) :
    ∀ᵐ ω ∂law p j, |p.coordinate i (point p hr side ω) - endpoint side (ω i)| ≤
      1 / (MixedRadix.radices p.q i : ℝ) := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  filter_upwards [ae_endpoint_unit hp j i side, ae_nonterminal_digits hp j hr side] with ω hunit hnt
  have hraw : endpoint side (ω i) ∈ bin _ (digits p hr side ω i) :=
    (UniformQuantization.quantize_eq_iff _ hunit).mp rfl
  exact (abs_sub_lt_bin_width _ (coordinate_point_mem_bin hp hr side ω hnt i) hraw).le

lemma ae_top_raw_support (j : ℕ) {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) (which : Bool) :
    ∀ᵐ ω ∂law p j, label i ω = topLabel which →
      1 - width (p.a s) (p.b s) which / 2 ≤ (ω i).2.2 := by
  let := coordinateLaw_isProbabilityMeasure hp j
  apply (measurePreserving_eval_infinitePi (coordinateLaw p j) i).quasiMeasurePreserving.ae
    (p := fun z => z.1 = topLabel which → 1 - width (p.a s) (p.b s) which / 2 ≤ z.2.2)
  have hi0 : i ≠ 0 := by have := (p.mem_block_iff s i).mp hi; omega
  rw [coordinateLaw, ite_eq_right hi0, p.blockIndex_eq_of_mem hp.m_pos hi]
  have hm : (100 : ℝ) ≤ p.m s := by exact_mod_cast (show 100 ≤ p.m s by have := hp.m_ge_200 s hs; omega)
  exact rawLaw_ae_top_support hm (hp.coupling_a_bounds s hs).1 (hp.coupling_a_bounds s hs).2
    (hp.coupling_b_bounds s hs).1 (hp.coupling_b_bounds s hs).2 which

lemma ae_bottom_raw_support (j : ℕ) {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) (which : Bool) :
    ∀ᵐ ω ∂law p j, label i ω = bottomLabel which →
      (ω i).2.1 < width (p.a s) (p.b s) which / 2 := by
  let := coordinateLaw_isProbabilityMeasure hp j
  apply (measurePreserving_eval_infinitePi (coordinateLaw p j) i).quasiMeasurePreserving.ae
    (p := fun z => z.1 = bottomLabel which → z.2.1 < width (p.a s) (p.b s) which / 2)
  have hi0 : i ≠ 0 := by have := (p.mem_block_iff s i).mp hi; omega
  rw [coordinateLaw, ite_eq_right hi0, p.blockIndex_eq_of_mem hp.m_pos hi]
  have hm : (100 : ℝ) ≤ p.m s := by exact_mod_cast (show 100 ≤ p.m s by have := hp.m_ge_200 s hs; omega)
  exact rawLaw_ae_bottom_support hm (hp.coupling_a_bounds s hs).1 (hp.coupling_a_bounds s hs).2
    (hp.coupling_b_bounds s hs).1 (hp.coupling_b_bounds s hs).2 which

lemma ae_top_forces (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) (which : Bool) :
    ∀ᵐ ω ∂law p j, ∀ u : ℝ, label i ω = topLabel which →
      u ≤ 1 - width (p.a s) (p.b s) which → u ≤ p.coordinate i (point p hr true ω) := by
  have hw : 1 / (p.m s : ℝ) ≤ width (p.a s) (p.b s) which := by
    cases which
    · exact (hp.coupling_a_bounds s hs).1
    · exact (hp.coupling_b_bounds s hs).1
  filter_upwards [ae_top_raw_support hp j hs hi which, ae_rounding_bound hp j hr i true] with ω hsupp hround
  intro u hl hu
  exact top_forces_crossing (hsupp hl) hround (hp.coupling_bin_small hs hi hw) hu

lemma ae_bottom_forces (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) (which : Bool) :
    ∀ᵐ ω ∂law p j, ∀ u : ℝ, label i ω = bottomLabel which →
      width (p.a s) (p.b s) which ≤ u → p.coordinate i (point p hr false ω) < u := by
  have hw : 1 / (p.m s : ℝ) ≤ width (p.a s) (p.b s) which := by
    cases which
    · exact (hp.coupling_a_bounds s hs).1
    · exact (hp.coupling_b_bounds s hs).1
  filter_upwards [ae_bottom_raw_support hp j hs hi which, ae_rounding_bound hp j hr i false] with ω hsupp hround
  intro u hl hu
  exact bottom_forces_crossing (hsupp hl) hround (hp.coupling_bin_small hs hi hw) hu

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleConditionalProbabilities
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling CouplingMarginalBounds
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma ae_top_conditional_probability (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) (which : Bool) :
    ∀ᵐ ω ∂law p j, ∀ u : ℝ,
      p.coordinate i (point p hr false ω) < u → u ≤ 1 - width (p.a s) (p.b s) which →
      rho (kappa s) (p.m s) (width (p.a s) (p.b s) which) / 10 ≤
        ((law p j)⟦label i ⁻¹' {topLabel which} |
          MeasurableSpace.comap (point p hr false) inferInstance⟧) ω := by
  let := posterior_isMarkov hp j false i
  have hρ0 : 0 ≤ rho (kappa s) (p.m s) (width (p.a s) (p.b s) which) :=
    rho_nonneg (CircleParameterLaws.coupling_kappa_bounds s hs).1
  filter_upwards [ae_top_posterior_lower hp j hr hs hi which,
    condExp_single_label_point hp j hr false i (topLabel which)] with ω hlo heq
  intro u hxu hu
  rw [heq]
  have h := ENNReal.toReal_mono (measure_ne_top _ _) (hlo u hxu hu)
  simpa only [measureReal_def, ENNReal.toReal_div, ENNReal.toReal_ofReal hρ0,
    ENNReal.toReal_ofNat] using h

lemma ae_bottom_conditional_probability (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) (which : Bool) :
    ∀ᵐ ω ∂law p j, ∀ u : ℝ,
      u ≤ p.coordinate i (point p hr true ω) → width (p.a s) (p.b s) which ≤ u →
      rho (kappa s) (p.m s) (width (p.a s) (p.b s) which) / 10 ≤
        ((law p j)⟦label i ⁻¹' {bottomLabel which} |
          MeasurableSpace.comap (point p hr true) inferInstance⟧) ω := by
  let := posterior_isMarkov hp j true i
  have hρ0 : 0 ≤ rho (kappa s) (p.m s) (width (p.a s) (p.b s) which) :=
    rho_nonneg (CircleParameterLaws.coupling_kappa_bounds s hs).1
  filter_upwards [ae_bottom_posterior_lower hp j hr hs hi which,
    condExp_single_label_point hp j hr true i (bottomLabel which)] with ω hlo heq
  intro u huy hu
  rw [heq]
  have h := ENNReal.toReal_mono (measure_ne_top _ _) (hlo u huy hu)
  simpa only [measureReal_def, ENNReal.toReal_div, ENNReal.toReal_ofReal hρ0,
    ENNReal.toReal_ofNat] using h

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingTagSupport
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

lemma rawLaw_ae_tag_left {κ m a b t : ℝ}
    (hm : 100 ≤ m) (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4) :
    ∀ᵐ z ∂rawLaw κ m a b t, z.1 = some 4 → z.2.1 < 1 / (2 * m) := by
  apply rawLaw_ae_endpoint_property hm ha ha' hb hb' false
    (P := fun l x => l = some 4 → x < 1 / (2 * m))
  · simp only [imp_iff_not_or, endpoint, Bool.false_eq_true, ite_false, if_false]
    exact (measurableSet_eq_fun measurable_fst measurable_const).compl.union
      (measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const)
  · exact Eventually.of_forall (by intro x h; cases h)
  · intro i
    by_cases hi : i = 4
    · subst i
      filter_upwards [intervalLaw_ae_mem 0 (1 / (2 * m))] with x hx
      exact fun _ => hx.2
    · exact Eventually.of_forall (fun _ h => (hi (Option.some.inj h)).elim)

lemma rawLaw_ae_tag_right {κ m a b t : ℝ}
    (hm : 100 ≤ m) (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4) :
    ∀ᵐ z ∂rawLaw κ m a b t, z.1 = some 4 → 1 - 1 / (2 * m) ≤ z.2.2 := by
  apply rawLaw_ae_endpoint_property hm ha ha' hb hb' true
    (P := fun l x => l = some 4 → 1 - 1 / (2 * m) ≤ x)
  · simp only [imp_iff_not_or, endpoint, ite_true, if_true]
    exact (measurableSet_eq_fun measurable_fst measurable_const).compl.union
      (measurableSet_le measurable_const (measurable_snd.comp measurable_snd))
  · exact Eventually.of_forall (by intro x h; cases h)
  · intro i
    by_cases hi : i = 4
    · subst i
      filter_upwards [intervalLaw_ae_mem (1 - 1 / (2 * m)) 1] with x hx
      exact fun _ => hx.1
    · exact Eventually.of_forall (fun _ h => (hi (Option.some.inj h)).elim)

end Invariant233.CircleDigitCoupling

namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma ae_tag_raw_support (j : ℕ) {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) :
    ∀ᵐ ω ∂law p j, label i ω = some 4 →
      (ω i).2.1 < 1 / (2 * (p.m s : ℝ)) ∧
        1 - 1 / (2 * (p.m s : ℝ)) ≤ (ω i).2.2 := by
  let := coordinateLaw_isProbabilityMeasure hp j
  apply (measurePreserving_eval_infinitePi (coordinateLaw p j) i).quasiMeasurePreserving.ae
    (p := fun z => z.1 = some 4 → z.2.1 < 1 / (2 * (p.m s : ℝ)) ∧
      1 - 1 / (2 * (p.m s : ℝ)) ≤ z.2.2)
  have hi0 : i ≠ 0 := by have := (p.mem_block_iff s i).mp hi; omega
  rw [coordinateLaw, ite_eq_right hi0, p.blockIndex_eq_of_mem hp.m_pos hi]
  have hm : (100 : ℝ) ≤ p.m s := by
    exact_mod_cast (show 100 ≤ p.m s by have := hp.m_ge_200 s hs; omega)
  filter_upwards [rawLaw_ae_tag_left hm (hp.coupling_a_bounds s hs).1
    (hp.coupling_a_bounds s hs).2 (hp.coupling_b_bounds s hs).1 (hp.coupling_b_bounds s hs).2,
    rawLaw_ae_tag_right hm (hp.coupling_a_bounds s hs).1
    (hp.coupling_a_bounds s hs).2 (hp.coupling_b_bounds s hs).1 (hp.coupling_b_bounds s hs).2]
      with z hl hr
  exact fun h => ⟨hl h, hr h⟩

lemma ae_tag_coordinate_support (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) :
    ∀ᵐ ω ∂law p j, label i ω = some 4 →
      p.coordinate i (point p hr false ω) < 1 / (p.m s : ℝ) ∧
        1 - 1 / (p.m s : ℝ) < p.coordinate i (point p hr true ω) := by
  have hsmall := hp.coupling_bin_small hs hi (le_refl (1 / (p.m s : ℝ)))
  have hhalf : (1 / (p.m s : ℝ)) / 2 = 1 / (2 * (p.m s : ℝ)) := by ring
  rw [hhalf] at hsmall
  have hsum : 1 / (2 * (p.m s : ℝ)) + 1 / (2 * (p.m s : ℝ)) =
      1 / (p.m s : ℝ) := by ring
  filter_upwards [ae_tag_raw_support hp j hs hi,
    ae_rounding_bound hp j hr i false, ae_rounding_bound hp j hr i true]
      with ω htag hx hy
  intro hl
  have hraw := htag hl
  have hx' := (abs_le.mp hx).2
  have hy' := (abs_le.mp hy).1
  simp only [endpoint, Bool.false_eq_true, ite_false, if_false, ite_true, if_true] at hx' hy'
  constructor <;> linarith [hraw.1, hraw.2]

lemma ae_all_tag_coordinate_support (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    ∀ᵐ ω ∂law p j, ∀ s, 1 ≤ s → ∀ i ∈ p.block s, label i ω = some 4 →
      p.coordinate i (point p hr false ω) < 1 / (p.m s : ℝ) ∧
        1 - 1 / (p.m s : ℝ) < p.coordinate i (point p hr true ω) := by
  exact ae_all_iff.mpr (fun s => ae_all_iff.mpr (fun hs =>
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun hi =>
      ae_tag_coordinate_support hp j hr hs hi))))

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ConditionalAvoidance
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Classical

namespace Invariant233.ConditionalAvoidance

variable {Ω ι : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsFiniteMeasure μ]

section ConditionalIndependence

variable [StandardBorelSpace Ω]

theorem iCondIndepSet_preimages {β : ι → Type*}
    [mβ : ∀ i, MeasurableSpace (β i)]
    (hm : m ≤ mΩ) (f : ∀ i, Ω → β i) (hf : ∀ i, Measurable (f i))
    (hind : iCondIndepFun m hm f μ) (C : ∀ i, Set (β i))
    (hC : ∀ i, MeasurableSet (C i)) :
    iCondIndepSet m hm (fun i => f i ⁻¹' C i) μ := by
  rw [iCondIndepSet_iff m hm _ (fun i => (hf i) (hC i)) μ]
  intro S
  exact (iCondIndepFun_iff_condExp_inter_preimage_eq_mul mβ f hf).mp hind S
    (fun i _ => hC i)

end ConditionalIndependence
end Invariant233.ConditionalAvoidance

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingAttenuation
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData CouplingMarginalBounds
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma actual_tail_attenuation_of_ac_order_oai (j : ℕ) (hj : 1 ≤ j)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (hac : ∀ side, (law p j).map (point p hr side) ≪ circleMeasure)
    (horder : ∀ᵐ ω ∂law p j, ∀ i : p.Coord,
      p.coordinate i.2 (point p hr false ω) ≤ p.coordinate i.2 (point p hr true ω)) :
    TailAttenuation θ p j hr := by
  let := law_isProbabilityMeasure hp j
  have hpoint (side : Bool) : Measurable[endpointSigma p hr side] (point p hr side) :=
    Measurable.of_comap_le le_rfl
  have hle (side : Bool) : endpointSigma p hr side ≤ (inferInstance : MeasurableSpace Sample) :=
    (measurable_point hp hr side).comap_le
  let top : Bool → ℕ → Set Sample := fun which i => label i ⁻¹' {topLabel which}
  let bottom : Bool → ℕ → Set Sample := fun which i => label i ⁻¹' {bottomLabel which}
  have ht (which : Bool) (i : ℕ) : MeasurableSet (top which i) :=
    (measurable_label i) (measurableSet_singleton _)
  have hb (which : Bool) (i : ℕ) : MeasurableSet (bottom which i) :=
    (measurable_label i) (measurableSet_singleton _)
  have hindt (which : Bool) : iCondIndepSet (endpointSigma p hr false) (hle false)
      (top which) (law p j) :=
    ConditionalAvoidance.iCondIndepSet_preimages (hle false) label measurable_label
      (iCondIndepFun_labels_point hp j hr false) (fun _ => {topLabel which})
      (fun _ => measurableSet_singleton _)
  have hindb (which : Bool) : iCondIndepSet (endpointSigma p hr true) (hle true)
      (bottom which) (law p j) :=
    ConditionalAvoidance.iCondIndepSet_preimages (hle true) label measurable_label
      (iCondIndepFun_labels_point hp j hr true) (fun _ => {bottomLabel which})
      (fun _ => measurableSet_singleton _)
  intro k hk
  apply hp.parameter_tail_conditional_attenuation (endpointSigma p hr false)
    (endpointSigma p hr true) (hle false) (hle true) (law p j)
    (point p hr false) (point p hr true) (hpoint false) (hpoint true)
    (hac false) (hac true) horder top bottom ht hb hindt hindb j hj
  · intro s hjs which i hi u hu
    have hs : 1 ≤ s := hj.trans hjs
    filter_upwards [ae_top_forces hp j hr hs hi which,
      ae_bottom_forces hp j hr hs hi which,
      ae_top_conditional_probability hp j hr hs hi which,
      ae_bottom_conditional_probability hp j hr hs hi which]
        with ω htforce hbforce htprob hbprob
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro _hxu hl
      exact htforce u hl hu.2
    · intro _huy hl
      exact hbforce u hl hu.1
    · intro hxu
      exact htprob u hxu hu.2
    · intro huy
      exact hbprob u huy hu.1
  · filter_upwards [ae_all_tag_coordinate_support hp j hr] with ω hω
    rintro ⟨i, hi, htag⟩
    exact ⟨i, hi, hω j hj i hi htag⟩
  · exact hk

end Invariant233.CircleCoupling

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.CircleCoupling.actual_tail_attenuation_of_ac_order_oai := @OAI.Invariant233.CircleCoupling.actual_tail_attenuation_of_ac_order_oai
