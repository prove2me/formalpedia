-- Prove2me | solution 1 for OAI.Invariant233.ProductScaleLaws.eventually_source_product_tail_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:34:12.459402+00:00
-- url     : https://prove2.me/submissions/80f36906-82fe-493a-a736-409e556eb8c2

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Find
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BlockAverageSum
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
namespace InvariantProjection.IndependentAngles

theorem tsum_fin_block_average {m : ℕ} (hm : 0 < m) (u : ℝ) :
    (∑' _i : Fin m, u / (m : ℝ)) = u := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

theorem summable_block_average (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    (u : ℕ → ℝ) (hu : ∀ s, 0 ≤ u s) (hsum : Summable u) :
    Summable (fun i : Σ s, Fin (m s) => u i.1 / (m i.1 : ℝ)) := by
  apply (summable_sigma_of_nonneg (fun i =>
    div_nonneg (hu i.1) (Nat.cast_nonneg _))).2
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa only [tsum_fin_block_average (hm _)] using hsum

theorem tsum_block_average (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    (u : ℕ → ℝ) (hu : ∀ s, 0 ≤ u s) (hsum : Summable u) :
    (∑' i : Σ s, Fin (m s), u i.1 / (m i.1 : ℝ)) = ∑' s, u s := by
  rw [(summable_block_average m hm u hu hsum).tsum_sigma'
    (fun _ => (hasSum_fintype _).summable)]
  simp only [tsum_fin_block_average (hm _)]

theorem enumerated_block_average {ι : Type*} (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    (u : ℕ → ℝ) (hu : ∀ s, 0 ≤ u s) (hsum : Summable u)
    (e : ι ≃ Σ s, Fin (m s)) :
    Summable (fun i => u (e i).1 / (m (e i).1 : ℝ)) ∧
    (∑' i, u (e i).1 / (m (e i).1 : ℝ)) = ∑' s, u s := by
  constructor
  · exact e.summable_iff.mpr (summable_block_average m hm u hu hsum)
  · exact (e.tsum_eq _).trans (tsum_block_average m hm u hu hsum)

end InvariantProjection.IndependentAngles

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_DensityTransport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.DensityTransport

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} {F : X → Y} {G : Y → X}

theorem map_inverse_eq (hF : Measurable F) (hG : Measurable G)
    (hmap : μ.map F = ν) (hinv : ∀ᵐ x ∂μ, G (F x) = x) : ν.map G = μ := by
  rw [← hmap, Measure.map_map hG hF]
  calc
    μ.map (G ∘ F) = μ.map id := Measure.map_congr hinv
    _ = μ := Measure.map_id

theorem map_withDensity_eq (hF : Measurable F) (hG : Measurable G)
    (hmap : μ.map F = ν) (hinv : ∀ᵐ x ∂μ, G (F x) = x)
    {h : X → ℝ≥0∞} (hh : Measurable h) :
    (μ.withDensity h).map F = ν.withDensity (h ∘ G) := by
  ext s hs
  rw [Measure.map_apply hF hs, withDensity_apply _ (hF hs), withDensity_apply _ hs,
    ← hmap, Measure.restrict_map hF hs,
    lintegral_map' (hh.comp hG).aemeasurable hF.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hinv] with x hx
  simp only [Function.comp_apply, hx]

theorem eLpNorm_comp_inverse {E : Type*} [NormedAddCommGroup E]
    (hF : Measurable F) (hG : Measurable G)
    (hmap : μ.map F = ν) (hinv : ∀ᵐ x ∂μ, G (F x) = x)
    {h : X → E} (hh : AEStronglyMeasurable h μ) (p : ℝ≥0∞) :
    eLpNorm (h ∘ G) p ν = eLpNorm h p μ := by
  exact eLpNorm_comp_measurePreserving hh
    ⟨hG, map_inverse_eq hF hG hmap hinv⟩

theorem real_density_transport (hF : Measurable F) (hG : Measurable G)
    (hmap : μ.map F = ν) (hinv : ∀ᵐ x ∂μ, G (F x) = x)
    {h : X → ℝ} (hh : Measurable h) :
    (μ.withDensity (fun x => ENNReal.ofReal (h x))).map F =
      ν.withDensity (fun y => ENNReal.ofReal (h (G y))) ∧
    eLpNorm (h ∘ G) 2 ν = eLpNorm h 2 μ := by
  constructor
  · exact map_withDensity_eq hF hG hmap hinv hh.ennreal_ofReal
  · exact eLpNorm_comp_inverse hF hG hmap hinv hh.aestronglyMeasurable 2

theorem real_density_transport_ae (hF : Measurable F) (hG : Measurable G)
    (hmap : μ.map F = ν) (hinv : ∀ᵐ x ∂μ, G (F x) = x)
    {h : X → ℝ} (hh : AEMeasurable h μ) :
    (μ.withDensity (fun x => ENNReal.ofReal (h x))).map F =
      ν.withDensity (fun y => ENNReal.ofReal (h (G y))) ∧
    eLpNorm (h ∘ G) 2 ν = eLpNorm h 2 μ := by
  have hback : ν.map G = μ := map_inverse_eq hF hG hmap hinv
  have ht : Filter.Tendsto G (ae ν) (ae μ) := by
    rw [← hback]
    exact Measure.tendsto_ae_map hG.aemeasurable
  have heq : h =ᵐ[μ] hh.mk h := hh.ae_eq_mk
  have heqG : h ∘ G =ᵐ[ν] hh.mk h ∘ G := heq.comp_tendsto ht
  obtain ⟨hweighted, hnorm⟩ := real_density_transport hF hG hmap hinv hh.measurable_mk
  constructor
  · have hx : μ.withDensity (fun x => ENNReal.ofReal (h x)) =
        μ.withDensity (fun x => ENNReal.ofReal (hh.mk h x)) := by
      apply withDensity_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]
    have hy : ν.withDensity (fun y => ENNReal.ofReal (h (G y))) =
        ν.withDensity (fun y => ENNReal.ofReal (hh.mk h (G y))) := by
      apply withDensity_congr_ae
      filter_upwards [heqG] with y hy
      exact congrArg ENNReal.ofReal hy
    rw [hx, hy]
    exact hweighted
  · calc
      eLpNorm (h ∘ G) 2 ν = eLpNorm (hh.mk h ∘ G) 2 ν := eLpNorm_congr_ae heqG
      _ = eLpNorm (hh.mk h) 2 μ := hnorm
      _ = eLpNorm h 2 μ := (eLpNorm_congr_ae heq).symm

end Invariant233.DensityTransport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FiniteKernelMixture
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
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

theorem normalizedKernel_disintegration (μ : Measure X) [SFinite μ]
    (κ : I → Kernel X Y) [∀ i, IsMarkovKernel (κ i)]
    (w : I → X → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (h0 : ∀ x, (∑ i, w i x) ≠ 0) (ht : ∀ x, (∑ i, w i x) ≠ ∞) :
    (μ.withDensity (fun x => ∑ i, w i x)) ⊗ₘ normalizedKernel κ w hw =
      ∑ i, (μ.withDensity (w i)) ⊗ₘ κ i := by
  let := normalizedKernel_isMarkov κ w hw h0 ht
  have hsum : Measurable (fun x => ∑ i, w i x) :=
    Finset.measurable_sum _ (fun i _ => hw i)
  ext s hs
  rw [Measure.compProd_apply hs,
    lintegral_withDensity_eq_lintegral_mul _ hsum
      (Kernel.measurable_kernel_prodMk_left hs)]
  simp only [normalizedKernel_apply, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  have heach (i : I) :
      ((μ.withDensity (w i)) ⊗ₘ κ i) s =
        ∫⁻ x, w i x * κ i x (Prod.mk x ⁻¹' s) ∂μ := by
    rw [Measure.compProd_apply hs,
      lintegral_withDensity_eq_lintegral_mul _ (hw i)
        (Kernel.measurable_kernel_prodMk_left hs)]
    rfl
  simp_rw [heach]
  calc
    _ = ∫⁻ x, ∑ i, w i x * κ i x (Prod.mk x ⁻¹' s) ∂μ := by
      apply lintegral_congr
      intro x
      change (∑ i, w i x) * (∑ i, (w i x / ∑ j, w j x) * κ i x (Prod.mk x ⁻¹' s)) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_assoc, ENNReal.mul_div_cancel (h0 x) (ht x)]
    _ = _ := lintegral_finsetSum _ (fun i _ =>
      (hw i).mul (Kernel.measurable_kernel_prodMk_left hs))

theorem diagonalReplacementKernel_apply (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u : I → X → ℝ≥0∞) (hu : ∀ i, Measurable (u i))
    (ν : I → Measure X) (x : X) :
    diagonalReplacementKernel q p u hu ν x =
      (q / (q + ∑ i, p i * u i x)) • Measure.dirac x +
        ∑ i, (p i * u i x / (q + ∑ j, p j * u j x)) • ν i := by
  simp only [diagonalReplacementKernel, normalizedKernel_apply,
    Fintype.sum_option, Kernel.id_apply, Kernel.const_apply]

theorem diagonalReplacementKernel_isMarkov (q : ℝ≥0∞) (hq : q ≠ 0)
    (p : I → ℝ≥0∞) (u : I → X → ℝ≥0∞) (hu : ∀ i, Measurable (u i))
    (ν : I → Measure X) [∀ i, IsProbabilityMeasure (ν i)]
    (ht : ∀ x, (q + ∑ i, p i * u i x) ≠ ∞) :
    IsMarkovKernel (diagonalReplacementKernel q p u hu ν) := by
  let κ : Option I → Kernel X X := fun o => match o with
    | none => Kernel.id
    | some i => Kernel.const X (ν i)
  have : ∀ o, IsMarkovKernel (κ o) := by
    intro o
    cases o <;> dsimp [κ] <;> infer_instance
  apply normalizedKernel_isMarkov (κ := κ)
  · intro x h
    have h' : q + ∑ i, p i * u i x = 0 := by
      simpa only [Fintype.sum_option] using h
    exact hq (add_eq_zero.mp h').1
  · intro x
    simpa only [Fintype.sum_option] using ht x

theorem diagonalReplacementKernel_disintegration (μ : Measure X) [SFinite μ]
    (q : ℝ≥0∞) (hq : q ≠ 0) (p : I → ℝ≥0∞)
    (u : I → X → ℝ≥0∞) (hu : ∀ i, Measurable (u i))
    (ν : I → Measure X) [∀ i, IsProbabilityMeasure (ν i)]
    (ht : ∀ x, (q + ∑ i, p i * u i x) ≠ ∞) :
    (μ.withDensity (fun x => q + ∑ i, p i * u i x)) ⊗ₘ
        diagonalReplacementKernel q p u hu ν =
      q • μ.map (fun x => (x, x)) +
        ∑ i, p i • (μ.withDensity (u i)).prod (ν i) := by
  let κ : Option I → Kernel X X := fun o => match o with
    | none => Kernel.id
    | some i => Kernel.const X (ν i)
  let w : Option I → X → ℝ≥0∞ := fun o x => match o with
    | none => q
    | some i => p i * u i x
  have hw : ∀ o, Measurable (w o) := by
    intro o
    cases o with
    | none => exact measurable_const
    | some i => exact measurable_const.mul (hu i)
  have : ∀ o, IsMarkovKernel (κ o) := by
    intro o
    cases o <;> dsimp [κ] <;> infer_instance
  have h0 (x : X) : (∑ o, w o x) ≠ 0 := by
    intro h
    have h' : q + ∑ i, p i * u i x = 0 := by
      simpa only [Fintype.sum_option, w] using h
    exact hq (add_eq_zero.mp h').1
  have hfin (x : X) : (∑ o, w o x) ≠ ∞ := by
    simpa only [Fintype.sum_option, w] using ht x
  have hdis := normalizedKernel_disintegration μ κ w hw h0 hfin
  simp only [Fintype.sum_option, κ, w] at hdis
  change (μ.withDensity (fun x => q + ∑ i, p i * u i x)) ⊗ₘ
    diagonalReplacementKernel q p u hu ν = _ at hdis
  rw [hdis]
  congr 1
  · rw [withDensity_const, Measure.compProd_smul_left, Measure.compProd_id]
    rfl
  · apply Finset.sum_congr rfl
    intro i _
    rw [Measure.compProd_const]
    change (μ.withDensity (p i • u i)).prod (ν i) = _
    rw [withDensity_smul (p i) (hu i), Measure.prod_smul_left]

theorem diagonalReplacementKernel_event_lower (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u : I → X → ℝ≥0∞) (hu : ∀ i, Measurable (u i))
    (ν : I → Measure X) (x : X) (s : Set X) (i : I) (C : ℝ≥0∞)
    (hui : 1 ≤ u i x) (hC : (q + ∑ j, p j * u j x) ≤ C)
    (hν : ν i s = 1) :
    p i / C ≤ diagonalReplacementKernel q p u hu ν x s := by
  classical
  rw [diagonalReplacementKernel_apply]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.finsetSum_apply]
  calc
    p i / C ≤ p i * u i x / (q + ∑ j, p j * u j x) := by
      apply ENNReal.div_le_div ?_ hC
      simpa only [mul_one] using mul_le_mul_right hui (p i)
    _ = (p i * u i x / (q + ∑ j, p j * u j x)) * ν i s := by rw [hν, mul_one]
    _ ≤ ∑ j, (p j * u j x / (q + ∑ k, p k * u k x)) * ν j s :=
      Finset.single_le_sum
        (f := fun j => (p j * u j x / (q + ∑ k, p k * u k x)) * ν j s)
        (fun _ _ => bot_le) (Finset.mem_univ i)
    _ ≤ _ := le_add_self

end Invariant233.FiniteKernelMixture

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ObservationConditioning
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Invariant233.ObservationConditioning

variable {Ω A B : Type*} [MeasurableSpace Ω]
    {mA : MeasurableSpace A} {mB : MeasurableSpace B}

theorem condExp_comap_congr_ae (μ : Measure Ω) [IsFiniteMeasure μ]
    {X X' : Ω → A} (hX : Measurable X) (hX' : Measurable X')
    (hXX' : X =ᵐ[μ] X') (f : Ω → ℝ) :
    μ[f | mA.comap X] =ᵐ[μ] μ[f | mA.comap X'] := by
  by_cases hf : Integrable f μ
  · have hkernel : condDistrib f X μ = condDistrib f X' μ :=
      condDistrib_congr_right hXX'
    filter_upwards [condExp_ae_eq_integral_condDistrib' hX hf,
      condExp_ae_eq_integral_condDistrib' hX' hf, hXX'] with ω h₁ h₂ hω
    rw [h₁, h₂, hkernel, hω]
  · simp only [condExp_of_not_integrable hf]
    rfl

theorem comap_eq_of_measurable_leftInverse {r : B → A} {q : A → B}
    (hr : Measurable r) (hq : Measurable q) (hqr : Function.LeftInverse q r) :
    mA.comap r = mB := by
  apply le_antisymm hr.comap_le
  intro s hs
  refine ⟨q ⁻¹' s, hq hs, ?_⟩
  ext b
  change q (r b) ∈ s ↔ b ∈ s
  rw [hqr b]

theorem condExp_comap_of_ae_section (μ : Measure Ω) [IsFiniteMeasure μ]
    {X : Ω → A} {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y)
    {r : B → A} {q : A → B} (hr : Measurable r) (hq : Measurable q)
    (hqr : Function.LeftInverse q r) (hrep : (r ∘ Y) =ᵐ[μ] X)
    (f : Ω → ℝ) :
    μ[f | mA.comap X] =ᵐ[μ] μ[f | mB.comap Y] := by
  have h := condExp_comap_congr_ae μ hX (hr.comp hY) hrep.symm f
  have heq : mA.comap (r ∘ Y) = mB.comap Y := by
    rw [← MeasurableSpace.comap_comp,
      comap_eq_of_measurable_leftInverse hr hq hqr]
  simpa only [heq] using h

theorem iCondIndepSet_comap_iff_of_ae_section {ι : Type*} [Countable ι]
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {X : Ω → A} {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y)
    {r : B → A} {q : A → B} (hr : Measurable r) (hq : Measurable q)
    (hqr : Function.LeftInverse q r) (hrep : (r ∘ Y) =ᵐ[μ] X)
    (events : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (events i)) :
    iCondIndepSet (mA.comap X) hX.comap_le events μ ↔
      iCondIndepSet (mB.comap Y) hY.comap_le events μ := by
  have hsingle : ∀ᵐ ω ∂μ, ∀ i,
      (μ[(events i).indicator (fun _ => (1 : ℝ)) | mA.comap X]) ω =
      (μ[(events i).indicator (fun _ => (1 : ℝ)) | mB.comap Y]) ω :=
    ae_all_iff.mpr (fun i => condExp_comap_of_ae_section μ hX hY hr hq hqr hrep _)
  rw [iCondIndepSet_iff _ _ events hmeas μ,
    iCondIndepSet_iff _ _ events hmeas μ]
  constructor
  · intro h S
    filter_upwards [h S, hsingle,
      condExp_comap_of_ae_section μ hX hY hr hq hqr hrep
        ((⋂ i ∈ S, events i).indicator (fun _ => (1 : ℝ)))] with ω hω hs hi
    rw [← hi, hω]
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl (fun i _ => hs i)
  · intro h S
    filter_upwards [h S, hsingle,
      condExp_comap_of_ae_section μ hX hY hr hq hqr hrep
        ((⋂ i ∈ S, events i).indicator (fun _ => (1 : ℝ)))] with ω hω hs hi
    rw [hi, hω]
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl (fun i _ => (hs i).symm)

omit [MeasurableSpace Ω] in

theorem iCondIndepSet_iff_of_events_ae_eq {ι : Type*} [Countable ι]
    (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (hm : m ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (events events' : ι → Set Ω)
    (hmeas : ∀ i, MeasurableSet (events i))
    (hmeas' : ∀ i, MeasurableSet (events' i))
    (heq : ∀ i, events i =ᵐ[μ] events' i) :
    iCondIndepSet m hm events μ ↔ iCondIndepSet m hm events' μ := by
  have hsingle : ∀ᵐ ω ∂μ, ∀ i,
      (μ[(events i).indicator (fun _ => (1 : ℝ)) | m]) ω =
      (μ[(events' i).indicator (fun _ => (1 : ℝ)) | m]) ω :=
    ae_all_iff.mpr (fun i => condExp_congr_ae (indicator_ae_eq_of_ae_eq_set (heq i)))
  have hinter (S : Finset ι) : (⋂ i ∈ S, events i) =ᵐ[μ] (⋂ i ∈ S, events' i) := by
    filter_upwards [ae_all_iff.mpr heq] with ω hω
    change (ω ∈ ⋂ i ∈ S, events i) = (ω ∈ ⋂ i ∈ S, events' i)
    apply propext
    simp only [Set.mem_iInter]
    constructor <;> intro h i hi
    · exact (hω i).mp (h i hi)
    · exact (hω i).mpr (h i hi)
  rw [iCondIndepSet_iff _ _ events hmeas μ,
    iCondIndepSet_iff _ _ events' hmeas' μ]
  constructor
  · intro h S
    filter_upwards [h S, hsingle,
      condExp_congr_ae (m := m)
        (indicator_ae_eq_of_ae_eq_set (f := fun _ => (1 : ℝ)) (hinter S))]
      with ω hω hs hi
    rw [← hi, hω]
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl (fun i _ => hs i)
  · intro h S
    filter_upwards [h S, hsingle,
      condExp_congr_ae (m := m)
        (indicator_ae_eq_of_ae_eq_set (f := fun _ => (1 : ℝ)) (hinter S))]
      with ω hω hs hi
    rw [hi, hω]
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl (fun i _ => (hs i).symm)

end Invariant233.ObservationConditioning

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

end Invariant233.FloorCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CouplingMarginalBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
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

lemma rho_sq_div_width {κ m w : ℝ} (hm : 0 < m) (hw : 0 < w) :
    (rho κ m w) ^ 2 / w = κ ^ 2 / m := by
  unfold rho
  rw [mul_pow, Real.sq_sqrt (div_nonneg hw.le hm.le)]
  field_simp

lemma marginal_density_bounds {κ m a b t u₁ u₂ u₃ u₄ v : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)
    (hu₁ : 0 ≤ u₁ ∧ u₁ ≤ 2 / a) (hu₂ : 0 ≤ u₂ ∧ u₂ ≤ 2 / a)
    (hu₃ : 0 ≤ u₃ ∧ u₃ ≤ 2 / b) (hu₄ : 0 ≤ u₄ ∧ u₄ ≤ 2 / b)
    (hv : 0 ≤ v ∧ v ≤ m) :
    let h := diagonalMass κ m a b t + rho κ m a * u₁ + rho κ m a * u₂ +
      rho κ m b * u₃ + rho κ m b * u₄ + (t / m) * v
    49 / 50 ≤ h ∧ h ≤ 2 + 8 * κ ∧ h < 10 := by
  dsimp only
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hra0 := rho_nonneg (m := m) (w := a) hκ0
  have hrb0 := rho_nonneg (m := m) (w := b) hκ0
  have hq := diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht
  have hra := rho_div_width_le hκ0 hm0 ha
  have hrb := rho_div_width_le hκ0 hm0 hb
  have hu₁' : rho κ m a * u₁ ≤ 2 * κ := by
    calc
      _ ≤ rho κ m a * (2 / a) := mul_le_mul_of_nonneg_left hu₁.2 hra0
      _ = 2 * (rho κ m a / a) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hra (by norm_num)
  have hu₂' : rho κ m a * u₂ ≤ 2 * κ := by
    calc
      _ ≤ rho κ m a * (2 / a) := mul_le_mul_of_nonneg_left hu₂.2 hra0
      _ = 2 * (rho κ m a / a) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hra (by norm_num)
  have hu₃' : rho κ m b * u₃ ≤ 2 * κ := by
    calc
      _ ≤ rho κ m b * (2 / b) := mul_le_mul_of_nonneg_left hu₃.2 hrb0
      _ = 2 * (rho κ m b / b) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrb (by norm_num)
  have hu₄' : rho κ m b * u₄ ≤ 2 * κ := by
    calc
      _ ≤ rho κ m b * (2 / b) := mul_le_mul_of_nonneg_left hu₄.2 hrb0
      _ = 2 * (rho κ m b / b) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrb (by norm_num)
  have htm0 := div_nonneg ht0 hm0.le
  have hv' : (t / m) * v ≤ t := by
    calc
      _ ≤ (t / m) * m := mul_le_mul_of_nonneg_left hv.2 htm0
      _ = t := div_mul_cancel₀ _ hm0.ne'
  have hlow₁ := mul_nonneg hra0 hu₁.1
  have hlow₂ := mul_nonneg hra0 hu₂.1
  have hlow₃ := mul_nonneg hrb0 hu₃.1
  have hlow₄ := mul_nonneg hrb0 hu₄.1
  have hlowv := mul_nonneg htm0 hv.1
  constructor
  · linarith [hq.1]
  constructor
  · linarith [hq.2]
  · linarith [hq.2]

lemma integral_sq_sum_le {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {μ : Measure Ω} {f : I → Ω → ℝ} (hf : ∀ i, MemLp (f i) 2 μ) :
    (∫ ω, (∑ i, f i ω) ^ 2 ∂μ) ≤
      (Fintype.card I : ℝ) * ∑ i, ∫ ω, (f i ω) ^ 2 ∂μ := by
  classical
  have hsum : MemLp (fun ω => ∑ i, f i ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ => hf i)
  have hsq : Integrable (fun ω => ∑ i, (f i ω) ^ 2) μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hf i).integrable_sq)
  calc
    _ ≤ ∫ ω, (Fintype.card I : ℝ) * ∑ i, (f i ω) ^ 2 ∂μ := by
      apply integral_mono hsum.integrable_sq (hsq.const_mul _)
      intro ω
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i => f i ω))
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum]
      intro i _
      exact (hf i).integrable_sq

lemma integral_sq_weighted_sum_le {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {μ : Measure Ω} {f : I → Ω → ℝ} (hf : ∀ i, MemLp (f i) 2 μ)
    (p : I → ℝ) :
    (∫ ω, (∑ i, p i * f i ω) ^ 2 ∂μ) ≤
      (Fintype.card I : ℝ) * ∑ i, (p i) ^ 2 * ∫ ω, (f i ω) ^ 2 ∂μ := by
  have h := integral_sq_sum_le (fun i => (hf i).const_mul (p i))
  simpa only [mul_pow, integral_const_mul] using h

lemma uniformDensity_memLp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω} (hs : MeasurableSet s)
    (p : ℝ≥0∞) : MemLp (uniformDensity μ s) p μ := by
  exact memLp_indicator_const p hs _ (Or.inr (measure_ne_top μ s))

lemma uniformDensity_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    ∫ ω, uniformDensity μ s ω ∂μ = 1 := by
  rw [uniformDensity, integral_indicator_const _ hs, smul_eq_mul]
  exact mul_inv_cancel₀ hpos.ne'

lemma uniformDensity_sq_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    ∫ ω, (uniformDensity μ s ω) ^ 2 ∂μ = (μ.real s)⁻¹ := by
  have hsq : (fun ω => (uniformDensity μ s ω) ^ 2) =
      s.indicator (fun _ => ((μ.real s)⁻¹) ^ 2) := by
    ext ω
    by_cases hω : ω ∈ s <;> simp [uniformDensity, hω]
  rw [hsq, integral_indicator_const _ hs, smul_eq_mul]
  field_simp

lemma uniformDensity_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Set Ω}
    (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    ∫ ω, (uniformDensity μ s ω - 1) ^ 2 ∂μ = (μ.real s)⁻¹ - 1 := by
  have hu := uniformDensity_memLp (μ := μ) hs 2
  have hui : Integrable (uniformDensity μ s) μ := hu.integrable (by norm_num)
  have hfun : (fun ω => (uniformDensity μ s ω - 1) ^ 2) =
      fun ω => (uniformDensity μ s ω) ^ 2 - 2 * uniformDensity μ s ω + 1 := by
    ext ω
    ring
  have hsub : Integrable (fun ω => (uniformDensity μ s ω) ^ 2 - 2 * uniformDensity μ s ω) μ :=
    hu.integrable_sq.sub (hui.const_mul 2)
  rw [hfun, integral_add hsub (integrable_const 1),
    integral_sub hu.integrable_sq (hui.const_mul 2), integral_const_mul,
    uniformDensity_sq_integral hs hpos, uniformDensity_integral hs hpos]
  simp
  ring

lemma uniformDensity_variance_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Set Ω}
    (hs : MeasurableSet s) {w : ℝ} (hw : 0 < w) (hlen : w / 2 ≤ μ.real s) :
    ∫ ω, (uniformDensity μ s ω - 1) ^ 2 ∂μ ≤ 2 / w := by
  have hpos : 0 < μ.real s := lt_of_lt_of_le (by positivity) hlen
  rw [uniformDensity_variance hs hpos]
  have hinv : (μ.real s)⁻¹ ≤ 2 / w := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hpos hw).2
    linarith
  linarith

lemma five_component_energy_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Fin 5 → Ω → ℝ} (hf : ∀ i, MemLp (f i) 2 μ)
    {κ m a b t : ℝ} (hm : 0 < m) (ha : 0 < a) (hb : 0 < b)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)
    (henergy : ∀ i, (∫ ω, (f i ω) ^ 2 ∂μ) ≤ componentVarianceBounds m a b i) :
    (∫ ω, (∑ i, componentProbabilities κ m a b t i * f i ω) ^ 2 ∂μ) ≤
      20 * (2 * κ ^ 2 / m + t / m) := by
  have hbound := integral_sq_weighted_sum_le hf (componentProbabilities κ m a b t)
  have hsum : (∑ i, (componentProbabilities κ m a b t i) ^ 2 *
      ∫ ω, (f i ω) ^ 2 ∂μ) ≤
      ∑ i, (componentProbabilities κ m a b t i) ^ 2 *
        componentVarianceBounds m a b i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (henergy i) (sq_nonneg _)
  have hcalc : (∑ i, (componentProbabilities κ m a b t i) ^ 2 *
      componentVarianceBounds m a b i) = 8 * κ ^ 2 / m + t ^ 2 / m := by
    simp only [componentProbabilities, componentVarianceBounds, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    have hra := rho_sq_div_width (κ := κ) hm ha
    have hrb := rho_sq_div_width (κ := κ) hm hb
    have htag : (t / m) ^ 2 * m = t ^ 2 / m := by field_simp
    rw [htag]
    simp only [div_eq_mul_inv] at hra hrb ⊢
    nlinarith
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have htdiv : t ^ 2 / m ≤ t / m := (div_le_div_iff_of_pos_right hm).2 ht2
  have htm : 0 ≤ t / m := div_nonneg ht0 hm.le
  norm_num only [Fintype.card_fin] at hbound
  calc
    _ ≤ 5 * (∑ i, (componentProbabilities κ m a b t i) ^ 2 *
        componentVarianceBounds m a b i) :=
      hbound.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))
    _ = 5 * (8 * κ ^ 2 / m + t ^ 2 / m) := by rw [hcalc]
    _ ≤ _ := by
      simp only [div_eq_mul_inv] at htdiv htm ⊢
      nlinarith

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

noncomputable section
open Set
open scoped BigOperators

namespace Invariant233.TailScaleCover

theorem exists_window
    (a b Q : ℕ → ℝ) (j : ℕ)
    (hgap : ∀ s, j ≤ s → a (s + 1) ≤ Q s)
    (hunbounded : ∀ R : ℝ, ∃ s, j ≤ s ∧ R ≤ Q s)
    {t : ℝ} (ht : b j ≤ t) :
    ∃ s, j ≤ s ∧
      ((b s ≤ t ∧ t ≤ Q s) ∨ (j < s ∧ a s ≤ t ∧ t ≤ b s)) := by
  classical
  let h := hunbounded t
  let s := Nat.find h
  have hs : j ≤ s ∧ t ≤ Q s := Nat.find_spec h
  refine ⟨s, hs.1, ?_⟩
  by_cases hb : b s ≤ t
  · exact Or.inl ⟨hb, hs.2⟩
  · right
    have hjs : j < s := by
      apply lt_of_le_of_ne hs.1
      intro heq
      exact hb (heq ▸ ht)
    have hprev : Q (s - 1) < t := by
      by_contra hnot
      have hsmall : s ≤ s - 1 := Nat.find_min' h ⟨by omega, le_of_not_gt hnot⟩
      omega
    have ha : a s ≤ t := by
      have hg := hgap (s - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ s)] at hg
      exact hg.trans hprev.le
    exact ⟨hjs, ha, le_of_not_ge hb⟩

theorem self_le_upperHorizon {m : ℕ} (hm : 2 ≤ m) :
    (m : ℝ) ≤ upperHorizon m := by
  apply Real.self_le_rpow_of_one_le
  · exact_mod_cast (show 1 ≤ m by omega)
  · have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith

theorem intensity_small (κ m G : ℝ) (hm : 0 < m) (hG : 0 ≤ G) :
    m * CouplingMarginalBounds.rho κ m (G / m) = κ * Real.sqrt G := by
  unfold CouplingMarginalBounds.rho
  have hdiv : (G / m) / m = G / m ^ 2 := by ring
  rw [hdiv, Real.sqrt_div hG, Real.sqrt_sq_eq_abs, abs_of_pos hm]
  field_simp

theorem intensity_large (κ m : ℝ) (hm : 0 < m) :
    m * CouplingMarginalBounds.rho κ m (m ^ (-(19 / 20 : ℝ))) =
      κ * m ^ (1 / 40 : ℝ) := by
  unfold CouplingMarginalBounds.rho
  rw [Real.sqrt_eq_rpow]
  have hdiv : m ^ (-(19 / 20 : ℝ)) / m = m ^ (-(39 / 20 : ℝ)) := by
    rw [show (-(39 / 20 : ℝ)) = -(19 / 20 : ℝ) - 1 by norm_num,
      Real.rpow_sub hm, Real.rpow_one]
  rw [hdiv, ← Real.rpow_mul hm.le]
  have hpow : m * m ^ ((-(39 / 20 : ℝ)) * (1 / 2 : ℝ)) =
      m ^ (1 / 40 : ℝ) := by
    calc
      _ = m ^ (1 : ℝ) * m ^ ((-(39 / 20 : ℝ)) * (1 / 2 : ℝ)) := by
        rw [Real.rpow_one]
      _ = m ^ (1 + (-(39 / 20 : ℝ)) * (1 / 2 : ℝ)) :=
        (Real.rpow_add hm _ _).symm
      _ = _ := by norm_num
  calc
    m * (κ * m ^ ((-(39 / 20 : ℝ)) * (1 / 2 : ℝ))) =
        κ * (m * m ^ ((-(39 / 20 : ℝ)) * (1 / 2 : ℝ))) := by ring
    _ = _ := by rw [hpow]

theorem widths_mem_Icc {m G : ℝ} (hm : 16 ≤ m) (hG : 1 ≤ G)
    (hGm : 4 * G ≤ m) :
    G / m ∈ Set.Icc (1 / m) (1 / 4) ∧
      m ^ (-(19 / 20 : ℝ)) ∈ Set.Icc (1 / m) (1 / 4) := by
  have hmpos : 0 < m := by linarith
  have hmone : 1 ≤ m := by linarith
  constructor
  · constructor
    · exact div_le_div_of_nonneg_right hG hmpos.le
    · apply (div_le_iff₀ hmpos).mpr
      linarith
  · rw [Real.rpow_neg hmpos.le, inv_eq_one_div]
    constructor
    · apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hmpos _)
      calc
        m ^ (19 / 20 : ℝ) ≤ m ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hmone (by norm_num)
        _ = m := Real.rpow_one _
    · apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
      have hsqrt : 4 ≤ Real.sqrt m := by
        nlinarith [Real.sq_sqrt hmpos.le, Real.sqrt_nonneg m]
      calc
        4 ≤ Real.sqrt m := hsqrt
        _ = m ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
        _ ≤ m ^ (19 / 20 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hmone (by norm_num)

end Invariant233.TailScaleCover

end
end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductDensity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.ProductDensity

theorem integral_sq_eq_one_add_centered_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {h : Ω → ℝ} (hh : MemLp h 2 μ) (hmean : ∫ x, h x ∂μ = 1) :
    (∫ x, h x ^ 2 ∂μ) = 1 + ∫ x, (h x - 1) ^ 2 ∂μ := by
  have hv := ProbabilityTheory.variance_eq_sub hh
  rw [ProbabilityTheory.variance_eq_integral hh.aemeasurable, hmean] at hv
  norm_num at hv
  linarith

theorem integral_finite_product_sq
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {h : (i : ι) → Ω i → ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1) :
    (∫ x, (∏ i, h i (x i)) ^ 2 ∂Measure.pi μ) =
      ∏ i, (1 + ∫ x, (h i x - 1) ^ 2 ∂μ i) := by
  calc
    _ = ∫ x, ∏ i, (h i (x i)) ^ 2 ∂Measure.pi μ := by
      congr 1
      funext x
      exact (Finset.prod_pow _ _ _).symm
    _ = ∏ i, ∫ x, (h i x) ^ 2 ∂μ i := integral_fintype_prod_eq_prod (μ := μ) (fun i x => h i x ^ 2)
    _ = _ := Finset.prod_congr rfl fun i _ =>
      integral_sq_eq_one_add_centered_sq (hh i) (hmean i)

theorem integral_finite_product_sq_le_exp
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {h : (i : ι) → Ω i → ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1) :
    (∫ x, (∏ i, h i (x i)) ^ 2 ∂Measure.pi μ) ≤
      Real.exp (∑ i, ∫ x, (h i x - 1) ^ 2 ∂μ i) := by
  rw [integral_finite_product_sq hh hmean]
  exact Real.prod_one_add_le_exp_sum _ fun i => integral_nonneg fun x => sq_nonneg _

theorem integral_finite_product_sq_le_exp_of_sum_le
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {h : (i : ι) → Ω i → ℝ} {C : ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hC : (∑ i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    (∫ x, (∏ i, h i (x i)) ^ 2 ∂Measure.pi μ) ≤ Real.exp C :=
  (integral_finite_product_sq_le_exp hh hmean).trans (Real.exp_le_exp.mpr hC)

theorem eLpNorm_finite_product_le_exp_half
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {h : (i : ι) → Ω i → ℝ} {C : ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hC : (∑ i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    eLpNorm (fun x => ∏ i, h i (x i)) 2 (Measure.pi μ) ≤
      ENNReal.ofReal (Real.exp (C / 2)) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    (memLp_finite_product hh)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (Real.exp C) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _)
        (integral_finite_product_sq_le_exp_of_sum_le hh hmean hC) (by positivity)
    _ = Real.exp (C / 2) := by
      rw [← Real.exp_mul]
      congr 1
      ring

theorem eLpNorm_partial_product_le_exp_half
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} {C : ℝ} (s : Finset ι)
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hC : (∑ i ∈ s, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    eLpNorm (fun x => ∏ i ∈ s, h i (x i)) 2 (Measure.infinitePi μ) ≤
      ENNReal.ofReal (Real.exp (C / 2)) := by
  have heq := eLpNorm_comp_measurePreserving
    (memLp_finite_product (fun i : s => hh i)).aestronglyMeasurable
    (measurePreserving_restrict_infinitePi μ s) (p := (2 : ℝ≥0∞))
  have hbound := eLpNorm_finite_product_le_exp_half (fun i : s => hh i)
    (fun i : s => hmean i) (C := C) (by
      exact (Finset.sum_coe_sort s (fun i => ∫ x, (h i x - 1) ^ 2 ∂μ i)).le.trans hC)
  rw [partial_product_eq_restrict h s]
  exact heq.le.trans hbound

theorem eLpNorm_partial_product_le_exp_half_of_tsum_le
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} {C : ℝ} (s : Finset ι)
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hsum : Summable (fun i => ∫ x, (h i x - 1) ^ 2 ∂μ i))
    (hC : (∑' i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    eLpNorm (fun x => ∏ i ∈ s, h i (x i)) 2 (Measure.infinitePi μ) ≤
      ENNReal.ofReal (Real.exp (C / 2)) := by
  apply eLpNorm_partial_product_le_exp_half s hh hmean
  exact (hsum.sum_le_tsum s fun i _ => integral_nonneg fun x => sq_nonneg _).trans hC

theorem integral_partial_product
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} (s : Finset ι)
    (hh : ∀ i, Integrable (h i) (μ i)) :
    (∫ x, ∏ i ∈ s, h i (x i) ∂Measure.infinitePi μ) =
      ∏ i ∈ s, ∫ x, h i x ∂μ i := by
  rw [partial_product_eq_restrict h s]
  change (∫ x, (fun y : (i : s) → Ω i => ∏ i : s, h i (y i)) (s.restrict x)
    ∂Measure.infinitePi μ) = _
  rw [integral_restrict_infinitePi (μ := μ) (s := s)
    (f := fun y : (i : s) → Ω i => ∏ i : s, h i (y i))
    (Integrable.fintype_prod_dep (fun i : s => hh i)).aestronglyMeasurable]
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_coe_sort s (fun i => ∫ x, h i x ∂μ i)

theorem partial_product_mul_of_subset
    {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    (h : (i : ι) → Ω i → ℝ) {s t : Finset ι} (hst : s ⊆ t) (x : (i : ι) → Ω i) :
    (∏ i ∈ s, h i (x i)) * (∏ i ∈ t, h i (x i)) =
      ∏ i ∈ t, if i ∈ s then h i (x i) ^ 2 else h i (x i) := by
  have heq : (∏ i ∈ t, if i ∈ s then h i (x i) else 1) =
      ∏ i ∈ s, h i (x i) := by
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hst]
  rw [← heq, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> ring

theorem integral_partial_product_mul_of_subset
    {ι : Type*} [DecidableEq ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} {s t : Finset ι} (hst : s ⊆ t)
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1) :
    (∫ x, (∏ i ∈ s, h i (x i)) * (∏ i ∈ t, h i (x i)) ∂Measure.infinitePi μ) =
      ∫ x, (∏ i ∈ s, h i (x i)) ^ 2 ∂Measure.infinitePi μ := by
  have hmixed : ∀ i, Integrable (fun x => if i ∈ s then h i x ^ 2 else h i x) (μ i) := by
    intro i
    by_cases hi : i ∈ s
    · simpa only [ite_eq_left hi] using (hh i).integrable_sq
    · simpa only [ite_eq_right hi] using (hh i).integrable (by norm_num)
  have hleft : (∫ x, (∏ i ∈ s, h i (x i)) * (∏ i ∈ t, h i (x i)) ∂Measure.infinitePi μ) =
      ∏ i ∈ s, ∫ x, h i x ^ 2 ∂μ i := by
    simp_rw [partial_product_mul_of_subset h hst]
    rw [integral_partial_product t hmixed]
    calc
      _ = ∏ i ∈ t, if i ∈ s then ∫ x, h i x ^ 2 ∂μ i else 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases his : i ∈ s
        · simp only [ite_eq_left his]
        · simp only [ite_eq_right his, hmean]
      _ = _ := by rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hst]
  rw [hleft]
  symm
  calc
    _ = ∫ x, ∏ i ∈ s, h i (x i) ^ 2 ∂Measure.infinitePi μ := by
      congr 1
      funext x
      exact (Finset.prod_pow _ _ _).symm
    _ = _ := integral_partial_product s (fun i => (hh i).integrable_sq)

theorem indicator_partial_product
    {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    (h : (i : ι) → Ω i → ℝ) {s t : Finset ι} (hst : s ⊆ t)
    (a : (i : ι) → Set (Ω i)) (x : (i : ι) → Ω i) :
    (Set.pi (s : Set ι) a).indicator (fun y => ∏ i ∈ t, h i (y i)) x =
      ∏ i ∈ t, if i ∈ s then (a i).indicator (h i) (x i) else h i (x i) := by
  classical
  by_cases hx : x ∈ Set.pi (s : Set ι) a
  · rw [Set.indicator_of_mem hx]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases his : i ∈ s
    · rw [ite_eq_left his, Set.indicator_of_mem ((Set.mem_pi.mp hx) i his)]
    · rw [ite_eq_right his]
  · rw [Set.indicator_of_notMem hx]
    symm
    have hex : ∃ i ∈ s, x i ∉ a i := by
      by_contra hnone
      apply hx
      apply Set.mem_pi.mpr
      intro i hi
      by_contra hix
      exact hnone ⟨i, hi, hix⟩
    obtain ⟨i, his, hix⟩ := hex
    apply Finset.prod_eq_zero (hst his)
    rw [ite_eq_left his, Set.indicator_of_notMem hix]

theorem setIntegral_partial_product_pi
    {ι : Type*} [DecidableEq ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} {s t : Finset ι} (hst : s ⊆ t)
    (hh : ∀ i, Integrable (h i) (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (a : (i : ι) → Set (Ω i)) (ha : ∀ i, MeasurableSet (a i)) :
    (∫ x in Set.pi (s : Set ι) a, ∏ i ∈ t, h i (x i) ∂Measure.infinitePi μ) =
      ∏ i ∈ s, ∫ x in a i, h i x ∂μ i := by
  classical
  have hmeas : MeasurableSet (Set.pi (s : Set ι) a) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ha i)
  rw [← integral_indicator hmeas]
  simp_rw [indicator_partial_product h hst a]
  have hmixed : ∀ i, Integrable (fun x => if i ∈ s then (a i).indicator (h i) x else h i x) (μ i) := by
    intro i
    by_cases his : i ∈ s
    · simpa only [ite_eq_left his] using (hh i).indicator (ha i)
    · simpa only [ite_eq_right his] using hh i
  rw [integral_partial_product t hmixed]
  calc
    _ = ∏ i ∈ t, if i ∈ s then ∫ x in a i, h i x ∂μ i else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases his : i ∈ s
      · simp only [ite_eq_left his, integral_indicator (ha i)]
      · simp only [ite_eq_right his, hmean]
    _ = _ := by rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hst]

end Invariant233.ProductDensity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_OrthogonalPrefixLimit
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.ProductDensity

theorem cauchySeq_of_prefix_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℕ → E)
    (hinner : ∀ n m, n ≤ m → inner ℝ (f n) (f m) = ‖f n‖ ^ 2)
    (hbound : BddAbove (Set.range fun n => ‖f n‖ ^ 2)) : CauchySeq f := by
  have hdist : ∀ n m, n ≤ m → dist (f n) (f m) ^ 2 = ‖f m‖ ^ 2 - ‖f n‖ ^ 2 := by
    intro n m hnm
    rw [dist_eq_norm, norm_sub_sq_real, hinner n m hnm]
    ring
  have hmono : Monotone (fun n => ‖f n‖ ^ 2) := by
    intro n m hnm
    have := sq_nonneg (dist (f n) (f m))
    rw [hdist n m hnm] at this
    linarith
  have hc : CauchySeq (fun n => ‖f n‖ ^ 2) :=
    (tendsto_atTop_ciSup hmono hbound).cauchySeq
  apply Metric.cauchySeq_iff.2
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hc (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn m hm => ?_⟩
  have hreal := hN n hn m hm
  rw [Real.dist_eq] at hreal
  rcases le_total n m with hnm | hmn
  · have hs := hdist n m hnm
    have hl := (abs_lt.mp hreal).1
    nlinarith [dist_nonneg (x := f n) (y := f m)]
  · have hs := hdist m n hmn
    have hl := (abs_lt.mp hreal).2
    rw [dist_comm (f m) (f n)] at hs
    nlinarith [dist_nonneg (x := f n) (y := f m)]

theorem exists_limit_of_prefix_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : ℕ → E)
    (hinner : ∀ n m, n ≤ m → inner ℝ (f n) (f m) = ‖f n‖ ^ 2)
    (hbound : BddAbove (Set.range fun n => ‖f n‖ ^ 2)) :
    ∃ g : E, Tendsto f atTop (𝓝 g) :=
  cauchySeq_tendsto_of_complete (cauchySeq_of_prefix_inner f hinner hbound)

end Invariant233.ProductDensity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductDensityLimit
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.ProductDensity

theorem inner_toLp_eq_integral_mul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  simp [hfx, hgx, mul_comm]

theorem partialDensityLp_inner
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1) {n m : ℕ} (hnm : n ≤ m) :
    inner ℝ (partialDensityLp hh n) (partialDensityLp hh m) =
      ‖partialDensityLp hh n‖ ^ 2 := by
  calc
    _ = ∫ x, (∏ i ∈ Finset.range n, h i (x i)) *
        (∏ i ∈ Finset.range m, h i (x i)) ∂Measure.infinitePi μ :=
      inner_toLp_eq_integral_mul _ _
    _ = ∫ x, (∏ i ∈ Finset.range n, h i (x i)) ^ 2 ∂Measure.infinitePi μ :=
      integral_partial_product_mul_of_subset (Finset.range_mono hnm) hh hmean
    _ = inner ℝ (partialDensityLp hh n) (partialDensityLp hh n) := by
      rw [partialDensityLp, inner_toLp_eq_integral_mul]
      congr 1
      funext x
      ring
    _ = _ := real_inner_self_eq_norm_sq _

theorem exists_partialDensityLp_limit
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} {C : ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hsum : Summable (fun i => ∫ x, (h i x - 1) ^ 2 ∂μ i))
    (hC : (∑' i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    ∃ g : Lp ℝ 2 (Measure.infinitePi μ),
      Tendsto (partialDensityLp hh) atTop (𝓝 g) ∧ ‖g‖ ≤ Real.exp (C / 2) := by
  have hb : ∀ n, ‖partialDensityLp hh n‖ ≤ Real.exp (C / 2) := by
    intro n
    rw [partialDensityLp, Lp.norm_toLp]
    have hnorm := eLpNorm_partial_product_le_exp_half_of_tsum_le
      (Finset.range n) hh hmean hsum hC
    have := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hnorm
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using this
  obtain ⟨g, hg⟩ := exists_limit_of_prefix_inner (partialDensityLp hh)
    (fun n m hnm => partialDensityLp_inner hh hmean hnm)
    ⟨(Real.exp (C / 2)) ^ 2, by
      rintro _ ⟨n, rfl⟩
      exact pow_le_pow_left₀ (norm_nonneg _) (hb n) 2⟩
  exact ⟨g, hg, le_of_tendsto hg.norm (Filter.Eventually.of_forall hb)⟩

theorem tendsto_eLpNorm_one_partialDensity_sub
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g)) :
    Tendsto (fun n => eLpNorm
      ((fun x => ∏ i ∈ Finset.range n, h i (x i)) - (g : ((i : ℕ) → Ω i) → ℝ))
      1 (Measure.infinitePi μ)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n => eLpNorm
      ((fun x => ∏ i ∈ Finset.range n, h i (x i)) - (g : ((i : ℕ) → Ω i) → ℝ))
      2 (Measure.infinitePi μ)) atTop (𝓝 0) := by
    have ht := hg.edist (tendsto_const_nhds (x := g))
    simp only [edist_self] at ht
    apply ht.congr
    intro n
    rw [Lp.edist_def]
    apply eLpNorm_congr_ae
    exact (memLp_partial_product (Finset.range n) hh).coeFn_toLp.sub Filter.EventuallyEq.rfl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
    (fun _ => bot_le)
  intro n
  exact eLpNorm_le_eLpNorm_of_exponent_le (hf := by first | exact (memLp_partial_product (Finset.range n) hh).aestronglyMeasurable.sub (Lp.aestronglyMeasurable g) | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num)

theorem partialDensityLp_limit_nonneg
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hnonneg : ∀ i x, 0 ≤ h i x)
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g)) :
    0 ≤ᵐ[Measure.infinitePi μ] (g : ((i : ℕ) → Ω i) → ℝ) := by
  apply ae_nonneg_of_forall_setIntegral_nonneg ((Lp.memLp g).integrable (by norm_num))
  intro s hs hsf
  have hi := tendsto_setIntegral_of_L1' (g : ((i : ℕ) → Ω i) → ℝ) (Lp.aestronglyMeasurable g)
    (Filter.Eventually.of_forall fun n =>
      (memLp_partial_product (Finset.range n) hh).integrable (by norm_num))
    (tendsto_eLpNorm_one_partialDensity_sub hh hg) s
  exact ge_of_tendsto hi (Filter.Eventually.of_forall fun n =>
    integral_nonneg fun x => Finset.prod_nonneg fun i _ => hnonneg i (x i))

theorem partialDensityLp_limit_integral
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g)) :
    (∫ x, g x ∂Measure.infinitePi μ) = 1 := by
  have hi := tendsto_integral_of_L1' (hfi := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (g : ((i : ℕ) → Ω i) → ℝ)
    (Filter.Eventually.of_forall fun n =>
      (memLp_partial_product (Finset.range n) hh).integrable (by norm_num))
    (tendsto_eLpNorm_one_partialDensity_sub hh hg)
  have heq : ∀ n, (∫ x, ∏ i ∈ Finset.range n, h i (x i) ∂Measure.infinitePi μ) = 1 := by
    intro n
    rw [integral_partial_product (Finset.range n) (fun i => (hh i).integrable (by norm_num))]
    simp [hmean]
  simp_rw [heq] at hi
  exact tendsto_nhds_unique hi tendsto_const_nhds

theorem partialDensityLp_limit_setIntegral_pi
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g))
    (s : Finset ℕ) (a : (i : ℕ) → Set (Ω i)) (ha : ∀ i, MeasurableSet (a i)) :
    (∫ x in Set.pi (s : Set ℕ) a, g x ∂Measure.infinitePi μ) =
      ∏ i ∈ s, ∫ x in a i, h i x ∂μ i := by
  have hi := tendsto_setIntegral_of_L1' (g : ((i : ℕ) → Ω i) → ℝ) (Lp.aestronglyMeasurable g)
    (Filter.Eventually.of_forall fun n =>
      (memLp_partial_product (Finset.range n) hh).integrable (by norm_num))
    (tendsto_eLpNorm_one_partialDensity_sub hh hg) (Set.pi (s : Set ℕ) a)
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range s
  have heq : (fun n => ∫ x in Set.pi (s : Set ℕ) a,
      ∏ i ∈ Finset.range n, h i (x i) ∂Measure.infinitePi μ) =ᶠ[atTop]
      (fun _ => ∏ i ∈ s, ∫ x in a i, h i x ∂μ i) := by
    apply Filter.eventually_atTop.2
    refine ⟨N, fun n hn => ?_⟩
    exact setIntegral_partial_product_pi (hN.trans (Finset.range_mono hn))
      (fun i => (hh i).integrable (by norm_num)) hmean a ha
  exact tendsto_nhds_unique hi (tendsto_const_nhds.congr' heq.symm)

theorem isProbabilityMeasure_withDensity_ofReal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {h : Ω → ℝ} (hh : Integrable h μ) (hnonneg : 0 ≤ᵐ[μ] h)
    (hmean : ∫ x, h x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (h x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hh hnonneg, hmean]
  simp

theorem partialDensityLp_limit_withDensity
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hnonneg : ∀ i x, 0 ≤ h i x)
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g)) :
    (Measure.infinitePi μ).withDensity (fun x => ENNReal.ofReal (g x)) =
      Measure.infinitePi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (h i x))) := by
  let : ∀ i, IsProbabilityMeasure ((μ i).withDensity (fun x => ENNReal.ofReal (h i x))) :=
    fun i => isProbabilityMeasure_withDensity_ofReal ((hh i).integrable (by norm_num))
      (Filter.Eventually.of_forall (hnonneg i)) (hmean i)
  have hgnonneg := partialDensityLp_limit_nonneg hh hnonneg hg
  have hgi := (Lp.memLp g).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply Measure.eq_infinitePi
  intro s a ha
  have hmeas : MeasurableSet (Set.pi (s : Set ℕ) a) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ha i)
  rw [withDensity_apply _ hmeas,
    ← ofReal_integral_eq_lintegral_ofReal hgi.restrict (ae_restrict_of_ae hgnonneg),
    partialDensityLp_limit_setIntegral_pi hh hmean hg s a ha]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hnonneg i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (ha i)]
  exact ofReal_integral_eq_lintegral_ofReal ((hh i).integrable (by norm_num)).restrict
    (Filter.Eventually.of_forall (hnonneg i))

theorem exists_product_density
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} {C : ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hnonneg : ∀ i x, 0 ≤ h i x)
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hsum : Summable (fun i => ∫ x, (h i x - 1) ^ 2 ∂μ i))
    (hC : (∑' i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    ∃ H : ((i : ℕ) → Ω i) → ℝ,
      MemLp H 2 (Measure.infinitePi μ) ∧
      (0 ≤ᵐ[Measure.infinitePi μ] H) ∧
      (∫ x, H x ∂Measure.infinitePi μ) = 1 ∧
      eLpNorm H 2 (Measure.infinitePi μ) ≤ ENNReal.ofReal (Real.exp (C / 2)) ∧
      (Measure.infinitePi μ).withDensity (fun x => ENNReal.ofReal (H x)) =
        Measure.infinitePi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (h i x))) := by
  obtain ⟨g, hg, hgbound⟩ := exists_partialDensityLp_limit hh hmean hsum hC
  refine ⟨g, Lp.memLp g, partialDensityLp_limit_nonneg hh hnonneg hg,
    partialDensityLp_limit_integral hh hmean hg, ?_,
    partialDensityLp_limit_withDensity hh hnonneg hmean hg⟩
  rw [← Lp.enorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hgbound

theorem exists_hybrid_product_density
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : Bool → (i : ℕ) → Ω i → ℝ} {b : ℕ → ℝ} {C : ℝ}
    (ε : ℕ → Bool)
    (hh : ∀ a i, MemLp (h a i) 2 (μ i))
    (hnonneg : ∀ a i x, 0 ≤ h a i x)
    (hmean : ∀ a i, ∫ x, h a i x ∂μ i = 1)
    (hb : ∀ a i, (∫ x, (h a i x - 1) ^ 2 ∂μ i) ≤ b i)
    (hsum : Summable b) (hC : (∑' i, b i) ≤ C) :
    ∃ H : ((i : ℕ) → Ω i) → ℝ,
      MemLp H 2 (Measure.infinitePi μ) ∧
      (0 ≤ᵐ[Measure.infinitePi μ] H) ∧
      (∫ x, H x ∂Measure.infinitePi μ) = 1 ∧
      eLpNorm H 2 (Measure.infinitePi μ) ≤ ENNReal.ofReal (Real.exp (C / 2)) ∧
      (Measure.infinitePi μ).withDensity (fun x => ENNReal.ofReal (H x)) =
        Measure.infinitePi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (h (ε i) i x))) := by
  have hsel : Summable (fun i => ∫ x, (h (ε i) i x - 1) ^ 2 ∂μ i) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg fun x => sq_nonneg _)
      (fun i => hb (ε i) i) hsum
  exact exists_product_density (fun i => hh (ε i) i)
    (fun i => hnonneg (ε i) i) (fun i => hmean (ε i) i) hsel
    ((hsel.tsum_le_tsum (fun i => hb (ε i) i) hsum).trans hC)

end Invariant233.ProductDensity

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

lemma diagonal_fst (μ : Measure X) : (diagonal μ).fst = μ := by
  simpa [diagonal] using
    (Measure.fst_map_prodMk (μ := μ) (X := id) (Y := id) measurable_id)

lemma diagonal_snd (μ : Measure X) : (diagonal μ).snd = μ := by
  simpa [diagonal] using
    (Measure.snd_map_prodMk (μ := μ) (X := id) (Y := id) measurable_id)

lemma fst_finsetSum {J : Type*} (s : Finset J) (μ : J → Measure (X × X)) :
    (∑ i ∈ s, μ i).fst = ∑ i ∈ s, (μ i).fst := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma snd_finsetSum {J : Type*} (s : Finset J) (μ : J → Measure (X × X)) :
    (∑ i ∈ s, μ i).snd = ∑ i ∈ s, (μ i).snd := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma mixture_fst (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (v i)] :
    (mixture μ q p u v).fst = q • μ + ∑ i, p i • u i := by
  unfold mixture
  rw [Measure.fst_add, fst_finsetSum]
  simp only [Measure.fst, Measure.map_smul,
    Measure.map_fst_prod, measure_univ, one_smul]
  rw [← Measure.fst, diagonal_fst]

lemma mixture_snd (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (u i)]
    [∀ i, IsProbabilityMeasure (v i)] :
    (mixture μ q p u v).snd = q • μ + ∑ i, p i • v i := by
  unfold mixture
  rw [Measure.snd_add, snd_finsetSum]
  simp only [Measure.snd, Measure.map_smul,
    Measure.map_snd_prod, measure_univ, one_smul]
  rw [← Measure.snd, diagonal_snd]

lemma diagonal_ae {μ : Measure X} {R : X → X → Prop}
    (hR : MeasurableSet {z : X × X | R z.1 z.2}) (href : ∀ x, R x x) :
    ∀ᵐ z ∂diagonal μ, R z.1 z.2 := by
  unfold diagonal
  apply (ae_map_iff (show Measurable (fun x : X => (x, x)) from
    measurable_id.prodMk measurable_id).aemeasurable hR).2
  exact Filter.Eventually.of_forall href

lemma mixture_ae {μ : Measure X} {q : ℝ≥0∞} {p : I → ℝ≥0∞}
    {u v : I → Measure X} {P : X × X → Prop}
    (hdiag : ∀ᵐ z ∂diagonal μ, P z)
    (hcomp : ∀ i, ∀ᵐ z ∂(u i).prod (v i), P z) :
    ∀ᵐ z ∂mixture μ q p u v, P z := by
  rw [mixture, ae_add_measure_iff, ae_finsetSum_measure_iff]
  exact ⟨Measure.ae_smul_measure hdiag q, fun i _ => Measure.ae_smul_measure (hcomp i) (p i)⟩

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

lemma mixture_fst_real_density (μ : Measure X) (q : ℝ) (p : I → ℝ)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (v i)]
    (g : I → X → ℝ) (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i)
    (hg0 : ∀ i x, 0 ≤ g i x) (hgm : ∀ i, Measurable (g i))
    (hu : ∀ i, u i = μ.withDensity (fun x => ENNReal.ofReal (g i x))) :
    (mixture μ (ENNReal.ofReal q) (fun i => ENNReal.ofReal (p i)) u v).fst =
      μ.withDensity (fun x => ENNReal.ofReal (q + ∑ i, p i * g i x)) := by
  rw [mixture_fst]
  simp_rw [hu, ofReal_mixture_density q p g hq hp hg0]
  exact (withDensity_finite_mixture μ _ _ _ (fun i => (hgm i).ennreal_ofReal)).symm

lemma mixture_snd_real_density (μ : Measure X) (q : ℝ) (p : I → ℝ)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (u i)]
    [∀ i, IsProbabilityMeasure (v i)]
    (g : I → X → ℝ) (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i)
    (hg0 : ∀ i x, 0 ≤ g i x) (hgm : ∀ i, Measurable (g i))
    (hv : ∀ i, v i = μ.withDensity (fun x => ENNReal.ofReal (g i x))) :
    (mixture μ (ENNReal.ofReal q) (fun i => ENNReal.ofReal (p i)) u v).snd =
      μ.withDensity (fun x => ENNReal.ofReal (q + ∑ i, p i * g i x)) := by
  rw [mixture_snd]
  simp_rw [hv, ofReal_mixture_density q p g hq hp hg0]
  exact (withDensity_finite_mixture μ _ _ _ (fun i => (hgm i).ennreal_ofReal)).symm

end Invariant233.CouplingMixture

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_OneCoordinateCoupling
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

lemma pairLaw_ae_ordered {κ m a b t : ℝ} (hm : 2 ≤ m) :
    ∀ᵐ z ∂pairLaw κ m a b t, z.1 ≤ z.2 := by
  apply mixture_ae
  · exact diagonal_ae (measurableSet_le measurable_fst measurable_snd) (fun _ => le_rfl)
  · exact replacement_ae_ordered hm

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

lemma labelledLaw_ae_ordered {κ m a b t : ℝ} (hm : 2 ≤ m) :
    ∀ᵐ z ∂labelledLaw κ m a b t, z.2.1 ≤ z.2.2 := by
  have h := pairLaw_ae_ordered (κ := κ) (a := a) (b := b) (t := t) hm
  rw [← labelledLaw_map_snd] at h
  exact (ae_map_iff measurable_snd.aemeasurable
    (measurableSet_le measurable_fst measurable_snd)).1 h

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_OneCoordinateDensity
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

lemma intervalDensity_memLp (a b : ℝ) (p : ℝ≥0∞) :
    MemLp (intervalDensity a b) p baseLaw :=
  uniformDensity_memLp measurableSet_Ico p

lemma intervalDensity_integral {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    (∫ x, intervalDensity a b x ∂baseLaw) = 1 := by
  apply uniformDensity_integral measurableSet_Ico
  rw [baseLaw_interval_measure ha hb hab.le]
  exact sub_pos.mpr hab

lemma intervalDensity_variance {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    (∫ x, (intervalDensity a b x - 1) ^ 2 ∂baseLaw) = (b - a)⁻¹ - 1 := by
  have hpos : 0 < baseLaw.real (Ico a b) := by
    rw [baseLaw_interval_measure ha hb hab.le]
    exact sub_pos.mpr hab
  rw [intervalDensity, uniformDensity_variance measurableSet_Ico hpos,
    baseLaw_interval_measure ha hb hab.le]

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

lemma pairLaw_fst_density {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (pairLaw κ m a b t).fst = baseLaw.withDensity
      (fun x => ENNReal.ofReal (leftMarginalDensity κ m a b t x)) := by
  have hm0 : 0 < m := by linarith
  have hm2 : 2 ≤ m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure hm2 ha0 ha' hb0 hb'
  apply mixture_fst_real_density
  · exact le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  · exact componentProbabilities_nonneg hκ0 hm0 ht0
  · intro i x
    exact (leftDensity_bound hm2 ha0 ha' hb0 hb' i x).1
  · intro i
    fin_cases i <;> exact intervalDensity_measurable _ _
  · exact leftLaw_eq_withDensity hm2 ha0 ha' hb0 hb'

lemma pairLaw_snd_density {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (pairLaw κ m a b t).snd = baseLaw.withDensity
      (fun x => ENNReal.ofReal (rightMarginalDensity κ m a b t x)) := by
  have hm0 : 0 < m := by linarith
  have hm2 : 2 ≤ m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (leftLaw m a b i) :=
    leftLaw_isProbabilityMeasure hm0 ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure hm2 ha0 ha' hb0 hb'
  apply mixture_snd_real_density
  · exact le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  · exact componentProbabilities_nonneg hκ0 hm0 ht0
  · intro i x
    exact (rightDensity_bound hm2 ha0 ha' hb0 hb' i x).1
  · intro i
    fin_cases i <;> exact intervalDensity_measurable _ _
  · exact rightLaw_eq_withDensity hm2 ha0 ha' hb0 hb'

lemma leftMarginalDensity_bounds {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) (x : ℝ) :
    49 / 50 ≤ leftMarginalDensity κ m a b t x ∧
      leftMarginalDensity κ m a b t x ≤ 2 + 8 * κ ∧
      leftMarginalDensity κ m a b t x < 10 := by
  have hm0 : 0 < m := by linarith
  have hd := leftDensity_bound (m := m) (by linarith) (width_pos hm0 ha) ha'
    (width_pos hm0 hb) hb'
  have h := marginal_density_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht
    (hd 0 x) (hd 1 x) (hd 2 x) (hd 3 x) (hd 4 x)
  simpa [leftMarginalDensity, componentProbabilities, Fin.sum_univ_succ, leftDensity, add_assoc] using h

lemma rightMarginalDensity_bounds {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) (x : ℝ) :
    49 / 50 ≤ rightMarginalDensity κ m a b t x ∧
      rightMarginalDensity κ m a b t x ≤ 2 + 8 * κ ∧
      rightMarginalDensity κ m a b t x < 10 := by
  have hm0 : 0 < m := by linarith
  have hd := rightDensity_bound (m := m) (by linarith) (width_pos hm0 ha) ha'
    (width_pos hm0 hb) hb'
  have h := marginal_density_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht
    (hd 0 x) (hd 1 x) (hd 2 x) (hd 3 x) (hd 4 x)
  simpa [rightMarginalDensity, componentProbabilities, Fin.sum_univ_succ, rightDensity, add_assoc] using h

lemma intervalDensity_variance_le_width {a b w : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hw : 0 < w) (hlen : w / 2 ≤ b - a) :
    (∫ x, (intervalDensity a b x - 1) ^ 2 ∂baseLaw) ≤ 2 / w := by
  apply uniformDensity_variance_le measurableSet_Ico hw
  rw [baseLaw_interval_measure ha hb (by linarith)]
  exact hlen

lemma leftDensity_variance_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    (∫ x, (leftDensity m a b i x - 1) ^ 2 ∂baseLaw) ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [leftDensity, componentVarianceBounds]
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · change (∫ x, (intervalDensity 0 (1 / m) x - 1) ^ 2 ∂baseLaw) ≤ m
    rw [intervalDensity_variance (by norm_num) (by linarith) hinv0]
    simp

lemma rightDensity_variance_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    (∫ x, (rightDensity m a b i x - 1) ^ 2 ∂baseLaw) ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [rightDensity, componentVarianceBounds]
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · change (∫ x, (intervalDensity (1 - 1 / m) 1 x - 1) ^ 2 ∂baseLaw) ≤ m
    rw [intervalDensity_variance (by linarith) (by norm_num) (by linarith)]
    simp

lemma marginalDensity_sub_one (κ m a b t : ℝ) (d : Fin 5 → ℝ) :
    diagonalMass κ m a b t + ∑ i, componentProbabilities κ m a b t i * d i - 1 =
      ∑ i, componentProbabilities κ m a b t i * (d i - 1) := by
  simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, diagonalMass]
  ring

lemma leftMarginalDensity_energy {κ m a b t : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (∫ x, (leftMarginalDensity κ m a b t x - 1) ^ 2 ∂baseLaw) ≤
      20 * (2 * κ ^ 2 / m + t / m) := by
  have hf : ∀ i, MemLp (fun x => leftDensity m a b i x - 1) 2 baseLaw := by
    intro i
    fin_cases i <;> exact (intervalDensity_memLp _ _ 2).sub (memLp_const 1)
  have h := five_component_energy_bound hf (κ := κ) (by linarith) ha0 hb0 ht0 ht
    (leftDensity_variance_bound hm ha0 ha1 hb0 hb1)
  simpa only [leftMarginalDensity, marginalDensity_sub_one] using h

lemma rightMarginalDensity_energy {κ m a b t : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (∫ x, (rightMarginalDensity κ m a b t x - 1) ^ 2 ∂baseLaw) ≤
      20 * (2 * κ ^ 2 / m + t / m) := by
  have hf : ∀ i, MemLp (fun x => rightDensity m a b i x - 1) 2 baseLaw := by
    intro i
    fin_cases i <;> exact (intervalDensity_memLp _ _ 2).sub (memLp_const 1)
  have h := five_component_energy_bound hf (κ := κ) (by linarith) ha0 hb0 ht0 ht
    (rightDensity_variance_bound hm ha0 ha1 hb0 hb1)
  simpa only [rightMarginalDensity, marginalDensity_sub_one] using h

lemma leftMarginalDensity_memLp (κ m a b t : ℝ) :
    MemLp (leftMarginalDensity κ m a b t) 2 baseLaw := by
  apply (memLp_const (diagonalMass κ m a b t)).add
  apply memLp_finsetSum Finset.univ
  intro i _
  apply MemLp.const_mul
  fin_cases i <;> exact intervalDensity_memLp _ _ 2

lemma rightMarginalDensity_memLp (κ m a b t : ℝ) :
    MemLp (rightMarginalDensity κ m a b t) 2 baseLaw := by
  apply (memLp_const (diagonalMass κ m a b t)).add
  apply memLp_finsetSum Finset.univ
  intro i _
  apply MemLp.const_mul
  fin_cases i <;> exact intervalDensity_memLp _ _ 2

lemma leftMarginalDensity_integral {κ m a b t : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) :
    (∫ x, leftMarginalDensity κ m a b t x ∂baseLaw) = 1 := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  have hi : ∀ i, Integrable (fun x => componentProbabilities κ m a b t i * leftDensity m a b i x) baseLaw := by
    intro i
    apply Integrable.const_mul
    fin_cases i <;> exact (intervalDensity_memLp _ _ 2).integrable (by first | (simp; all_goals first | (norm_num; done) | rfl | decide) | (norm_num; done) | norm_num)
  have hmean : ∀ i, (∫ x, leftDensity m a b i x ∂baseLaw) = 1 := by
    intro i
    fin_cases i <;> apply intervalDensity_integral <;> linarith
  have hs := integrable_finsetSum Finset.univ (fun i _ => hi i)
  change (∫ x, diagonalMass κ m a b t + ∑ i, componentProbabilities κ m a b t i * leftDensity m a b i x ∂baseLaw) = 1
  rw [integral_add (integrable_const _) hs,
    integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [integral_const, probReal_univ, one_smul,
    integral_const_mul, hmean, mul_one]
  simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, diagonalMass]
  ring

lemma rightMarginalDensity_integral {κ m a b t : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) :
    (∫ x, rightMarginalDensity κ m a b t x ∂baseLaw) = 1 := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  have hi : ∀ i, Integrable (fun x => componentProbabilities κ m a b t i * rightDensity m a b i x) baseLaw := by
    intro i
    apply Integrable.const_mul
    fin_cases i <;> exact (intervalDensity_memLp _ _ 2).integrable (by first | (simp; all_goals first | (norm_num; done) | rfl | decide) | (norm_num; done) | norm_num)
  have hmean : ∀ i, (∫ x, rightDensity m a b i x ∂baseLaw) = 1 := by
    intro i
    fin_cases i <;> apply intervalDensity_integral <;> linarith
  have hs := integrable_finsetSum Finset.univ (fun i _ => hi i)
  change (∫ x, diagonalMass κ m a b t + ∑ i, componentProbabilities κ m a b t i * rightDensity m a b i x ∂baseLaw) = 1
  rw [integral_add (integrable_const _) hs,
    integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [integral_const, probReal_univ, one_smul,
    integral_const_mul, hmean, mul_one]
  simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, diagonalMass]
  ring

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductCoupling
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.flatten_unflatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace Invariant233.OrderedProductCoupling

open OneCoordinateCoupling

lemma hybridEndpoint_measurable (ε : ℕ → Bool) : Measurable (hybridEndpoint ε) := by
  apply Measurable.of_eval
  intro i
  unfold hybridEndpoint rightEndpoint leftEndpoint
  split_ifs <;> fun_prop

lemma coordinateLaw_map_pair (P : Parameters) (i : ℕ) :
    (coordinateLaw P i).map Prod.snd = pairLaw (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i) :=
  labelledLaw_map_snd _ _ _ _ _

lemma coordinateLaw_map_left (P : Parameters) (i : ℕ) :
    (coordinateLaw P i).map (fun z => z.2.1) = baseLaw.withDensity
      (fun x => ENNReal.ofReal (marginalDensity P false i x)) := by
  have h := pairLaw_fst_density (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
    (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i) (P.t_nonneg i) (P.t_le i)
  rw [← coordinateLaw_map_pair P i, Measure.fst,
    Measure.map_map measurable_fst measurable_snd] at h
  exact h

lemma coordinateLaw_map_right (P : Parameters) (i : ℕ) :
    (coordinateLaw P i).map (fun z => z.2.2) = baseLaw.withDensity
      (fun x => ENNReal.ofReal (marginalDensity P true i x)) := by
  have h := pairLaw_snd_density (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
    (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i) (P.t_nonneg i) (P.t_le i)
  rw [← coordinateLaw_map_pair P i, Measure.snd,
    Measure.map_map measurable_snd measurable_snd] at h
  exact h

lemma hybridEndpoint_map (P : Parameters) (ε : ℕ → Bool) :
    (law P).map (hybridEndpoint ε) = Measure.infinitePi (fun i => baseLaw.withDensity
      (fun x => ENNReal.ofReal (marginalDensity P (ε i) i x))) := by
  let f : ℕ → CoordinateSample → ℝ :=
    fun i z => if ε i then z.2.2 else z.2.1
  have hf : ∀ i, Measurable (f i) := by
    intro i
    dsimp [f]
    split_ifs <;> fun_prop
  calc
    _ = Measure.infinitePi (fun i => (coordinateLaw P i).map (f i)) :=
      Measure.infinitePi_map_pi (coordinateLaw P) hf
    _ = _ := by
      congr 1
      funext i
      cases h : ε i
      · simpa only [f, h, Bool.false_eq_true, ite_false, if_false] using coordinateLaw_map_left P i
      · simpa only [f, h, ite_true, if_true] using coordinateLaw_map_right P i

lemma ae_ordered (P : Parameters) :
    ∀ᵐ ω ∂law P, ∀ i, leftEndpoint ω i ≤ rightEndpoint ω i := by
  apply ae_all_iff.2
  intro i
  have h : ∀ᵐ z ∂coordinateLaw P i, z.2.1 ≤ z.2.2 :=
    labelledLaw_ae_ordered (by linarith [P.m_ge i])
  exact (measurePreserving_eval_infinitePi (coordinateLaw P) i).quasiMeasurePreserving.ae h

lemma marginalDensity_memLp (P : Parameters) (side : Bool) (i : ℕ) :
    MemLp (marginalDensity P side i) 2 baseLaw := by
  cases side
  · exact leftMarginalDensity_memLp _ _ _ _ _
  · exact rightMarginalDensity_memLp _ _ _ _ _

lemma marginalDensity_nonneg (P : Parameters) (side : Bool) (i : ℕ) (x : ℝ) :
    0 ≤ marginalDensity P side i x := by
  cases side
  · exact le_trans (by norm_num) (leftMarginalDensity_bounds (P.κ_nonneg i) (P.κ_le i)
      (P.m_ge i) (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i) x).1
  · exact le_trans (by norm_num) (rightMarginalDensity_bounds (P.κ_nonneg i) (P.κ_le i)
      (P.m_ge i) (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i) x).1

lemma marginalDensity_integral (P : Parameters) (side : Bool) (i : ℕ) :
    (∫ x, marginalDensity P side i x ∂baseLaw) = 1 := by
  have hm0 : 0 < P.m i := by linarith [P.m_ge i]
  have ha0 := CouplingMarginalBounds.width_pos hm0 (P.a_lower i)
  have hb0 := CouplingMarginalBounds.width_pos hm0 (P.b_lower i)
  cases side
  · exact leftMarginalDensity_integral (by linarith [P.m_ge i]) ha0 (P.a_upper i) hb0 (P.b_upper i)
  · exact rightMarginalDensity_integral (by linarith [P.m_ge i]) ha0 (P.a_upper i) hb0 (P.b_upper i)

lemma marginalDensity_variance_le (P : Parameters) (side : Bool) (i : ℕ) :
    (∫ x, (marginalDensity P side i x - 1) ^ 2 ∂baseLaw) ≤ energyBound P i := by
  have hm0 : 0 < P.m i := by linarith [P.m_ge i]
  have ha0 := CouplingMarginalBounds.width_pos hm0 (P.a_lower i)
  have hb0 := CouplingMarginalBounds.width_pos hm0 (P.b_lower i)
  cases side
  · exact leftMarginalDensity_energy (by linarith [P.m_ge i]) ha0 (P.a_upper i) hb0 (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)
  · exact rightMarginalDensity_energy (by linarith [P.m_ge i]) ha0 (P.a_upper i) hb0 (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)

lemma exists_hybrid_density (P : Parameters) (ε : ℕ → Bool) {C : ℝ}
    (hsum : Summable (energyBound P)) (hC : (∑' i, energyBound P i) ≤ C) :
    ∃ H : Endpoint → ℝ, MemLp H 2 baseMeasure ∧ (0 ≤ᵐ[baseMeasure] H) ∧
      (∫ x, H x ∂baseMeasure) = 1 ∧
      eLpNorm H 2 baseMeasure ≤ ENNReal.ofReal (Real.exp (C / 2)) ∧
      (law P).map (hybridEndpoint ε) = baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) := by
  obtain ⟨H, hH, hnonneg, hmean, hnorm, hlaw⟩ :=
    ProductDensity.exists_hybrid_product_density ε
      (marginalDensity_memLp P) (marginalDensity_nonneg P) (marginalDensity_integral P)
      (marginalDensity_variance_le P) hsum hC
  exact ⟨H, hH, hnonneg, hmean, hnorm, (hybridEndpoint_map P ε).trans hlaw.symm⟩

end Invariant233.OrderedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_BlockProductCoupling
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Invariant233.OrderedProductCoupling
open InvariantProjection.IndependentAngles

lemma summable_sourceKappa_sq : Summable (fun s => sourceKappa s ^ 2) := by
  have hbase : Summable (fun s : ℕ => 1 / ((s + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.mpr (by norm_num))
  apply (hbase.mul_left (1 / 10000 : ℝ)).congr
  intro s
  have hs : (s : ℝ) + 1 ≠ 0 := by positivity
  simp only [sourceKappa, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

section BlockData
variable (m : ℕ → ℕ) (κ a b : ℕ → ℝ)
    (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
    (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (tag : ℕ)

lemma energyBound_ofBlocks (i : ℕ) :
    energyBound (ofBlocks m κ a b hκ0 hκ hm ha ha' hb hb' e tag) i =
      (20 * (2 * κ (e i).1 ^ 2 + if (e i).1 = tag then 1 else 0)) /
        (m (e i).1 : ℝ) := by
  unfold energyBound ofBlocks
  ring

theorem ofBlocks_energy_sum (hsκ : Summable (fun s => κ s ^ 2)) :
    Summable (energyBound (ofBlocks m κ a b hκ0 hκ hm ha ha' hb hb' e tag)) ∧
    (∑' i, energyBound (ofBlocks m κ a b hκ0 hκ hm ha ha' hb hb' e tag) i) =
      20 * (2 * (∑' s, κ s ^ 2) + 1) := by
  let u : ℕ → ℝ := fun s => 20 * (2 * κ s ^ 2 + if s = tag then 1 else 0)
  have hu : ∀ s, 0 ≤ u s := by
    intro s
    dsimp [u]
    split_ifs <;> positivity
  have htag : Summable (fun s : ℕ => if s = tag then (1 : ℝ) else 0) :=
    (hasSum_ite_eq tag (1 : ℝ)).summable
  have hsu : Summable u := ((hsκ.mul_left 2).add htag).mul_left 20
  have hblock := enumerated_block_average m (fun s => by have := hm s; omega) u hu hsu e
  have henergy : energyBound (ofBlocks m κ a b hκ0 hκ hm ha ha' hb hb' e tag) =
      fun i => u (e i).1 / (m (e i).1 : ℝ) := by
    funext i
    exact energyBound_ofBlocks m κ a b hκ0 hκ hm ha ha' hb hb' e tag i
  rw [henergy]
  refine ⟨hblock.1, hblock.2.trans ?_⟩
  dsimp [u]
  rw [tsum_mul_left, (hsκ.mul_left 2).tsum_add htag, tsum_mul_left,
    tsum_ite_eq]

end BlockData

end Invariant233.OrderedProductCoupling

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
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ConditionalEventBridge
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Invariant233.ConditionalEventBridge

variable {Ω A B ι : Type*}
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
  [Countable ι]

theorem iCondIndepSet_preimage_of_condDistrib
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → A) (Y : Ω → B) (hX : Measurable X) (hY : Measurable Y)
    (s : ι → Set B) (hs : ∀ i, MeasurableSet (s i))
    (hind : ∀ᵐ x ∂μ.map X, iIndepSet s (condDistrib Y X μ x)) :
    iCondIndepSet (MeasurableSpace.comap X inferInstance) hX.comap_le
      (fun i => Y ⁻¹' s i) μ := by
  apply (iCondIndepSet_iff _ _ _ (fun i => hY (hs i)) μ).2
  intro S
  have hi : ∀ᵐ ω ∂μ, ∀ i,
      (condDistrib Y X μ (X ω)).real (s i) =
        (μ[(Y ⁻¹' s i).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap X inferInstance]) ω :=
    ae_all_iff.mpr (fun i => condDistrib_ae_eq_condExp hX hY (hs i))
  have hinter := condDistrib_ae_eq_condExp (μ := μ) hX hY
    (MeasurableSet.biInter S.countable_toSet (fun i _ => hs i))
  have hind' := ae_of_ae_map hX.aemeasurable hind
  filter_upwards [hi, hinter, hind'] with ω hω hI hInd
  simp only [Set.preimage_iInter, Finset.mem_coe] at hI
  rw [← hI]
  have heq := congrArg ENNReal.toReal (hInd.meas_biInter S)
  simp only [ENNReal.toReal_prod] at heq
  change (condDistrib Y X μ (X ω)).real (⋂ i ∈ S, s i) = _ at heq
  rw [heq]
  simp only [Finset.prod_apply]
  exact Finset.prod_congr rfl (fun i _ => hω i)

end Invariant233.ConditionalEventBridge

end

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

theorem simultaneous_exceptional_families {κ : Type*} [Countable κ]
    (mx my : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (E : Set Ω) (R : κ → Ω → ℝ) (η δ : κ → ℝ)
    (h : ∀ k, ∃ H₁ H₂ : Set Ω, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂μ, (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ δ k) ∧
      (∀ᵐ ω ∂μ, (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ δ k) ∧
      (∀ᵐ ω ∂μ, ω ∈ E → R k ω ≤ η k + H₁.indicator (fun _ => (1 : ℝ)) ω +
        H₂.indicator (fun _ => (1 : ℝ)) ω)) :
    ∃ H₁ H₂ : κ → Set Ω, (∀ k, MeasurableSet (H₁ k)) ∧ (∀ k, MeasurableSet (H₂ k)) ∧
      (∀ᵐ ω ∂μ, ∀ k,
        (μ[(H₁ k).indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ δ k ∧
        (μ[(H₂ k).indicator (fun _ => (1 : ℝ)) | my]) ω ≤ δ k ∧
        (ω ∈ E → R k ω ≤ η k + (H₁ k).indicator (fun _ => (1 : ℝ)) ω +
          (H₂ k).indicator (fun _ => (1 : ℝ)) ω)) := by
  classical
  choose H₁ H₂ hmeas₁ hmeas₂ hbound₁ hbound₂ hratio using h
  refine ⟨H₁, H₂, hmeas₁, hmeas₂, ae_all_iff.mpr ?_⟩
  intro k
  filter_upwards [hbound₁ k, hbound₂ k, hratio k] with ω h₁ h₂ hr
  exact ⟨h₁, h₂, hr⟩

end Invariant233.CrossingAvoidance

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_OneCoordinateConditional
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace Invariant233.OneCoordinateCoupling
open CouplingMixture CouplingMarginalBounds FiniteKernelMixture

private lemma finite_total (q : ℝ) (p : Fin 5 → ℝ) (u : Fin 5 → ℝ → ℝ) (x : ℝ) :
    ENNReal.ofReal q + ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (u i x) ≠ ∞ := by
  apply ENNReal.add_ne_top.mpr
  refine ⟨ENNReal.ofReal_ne_top, ENNReal.sum_ne_top.mpr ?_⟩
  intro i _
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

section SourceParameters
variable {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)
include hκ0 hκ hm ha ha' hb hb' ht0 ht

lemma rightGivenLeft_isMarkov : IsMarkovKernel (rightGivenLeft κ m a b t) := by
  have hm0 : 0 < m := by linarith
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) (width_pos hm0 ha) ha' (width_pos hm0 hb) hb'
  apply diagonalReplacementKernel_isMarkov
  · apply ENNReal.ofReal_ne_zero_iff.mpr
    have := (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
    linarith
  · exact finite_total _ _ _

lemma leftGivenRight_isMarkov : IsMarkovKernel (leftGivenRight κ m a b t) := by
  have hm0 : 0 < m := by linarith
  have : ∀ i, IsProbabilityMeasure (leftLaw m a b i) :=
    leftLaw_isProbabilityMeasure hm0 (width_pos hm0 ha) ha' (width_pos hm0 hb) hb'
  apply diagonalReplacementKernel_isMarkov
  · apply ENNReal.ofReal_ne_zero_iff.mpr
    have := (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
    linarith
  · exact finite_total _ _ _

lemma rightGivenLeft_disintegration :
    (pairLaw κ m a b t).fst ⊗ₘ rightGivenLeft κ m a b t = pairLaw κ m a b t := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have := rightGivenLeft_isMarkov hκ0 hκ hm ha ha' hb hb' ht0 ht
  have hq : ENNReal.ofReal (diagonalMass κ m a b t) ≠ 0 := by
    apply ENNReal.ofReal_ne_zero_iff.mpr
    have := (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
    linarith
  let d : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (diagonalMass κ m a b t) +
    ∑ i, ENNReal.ofReal (componentProbabilities κ m a b t i) *
      ENNReal.ofReal (leftDensity m a b i x)
  have hpair : (baseLaw.withDensity d) ⊗ₘ rightGivenLeft κ m a b t = pairLaw κ m a b t := by
    unfold rightGivenLeft d
    rw [diagonalReplacementKernel_disintegration _ _ hq]
    · unfold pairLaw mixture CouplingMixture.diagonal
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [leftLaw_eq_withDensity (by linarith) ha0 ha' hb0 hb']
    · exact finite_total _ _ _
  have hfst := congrArg Measure.fst hpair
  rw [Measure.fst_compProd] at hfst
  rw [← hfst]
  exact hpair

lemma leftGivenRight_disintegration :
    (pairLaw κ m a b t).snd ⊗ₘ leftGivenRight κ m a b t =
      (pairLaw κ m a b t).map Prod.swap := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (leftLaw m a b i) :=
    leftLaw_isProbabilityMeasure hm0 ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have := leftGivenRight_isMarkov hκ0 hκ hm ha ha' hb hb' ht0 ht
  have hq : ENNReal.ofReal (diagonalMass κ m a b t) ≠ 0 := by
    apply ENNReal.ofReal_ne_zero_iff.mpr
    have := (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
    linarith
  have hswap : (pairLaw κ m a b t).map Prod.swap =
      ENNReal.ofReal (diagonalMass κ m a b t) • CouplingMixture.diagonal baseLaw +
        ∑ i, ENNReal.ofReal (componentProbabilities κ m a b t i) •
          (rightLaw m a b i).prod (leftLaw m a b i) := by
    unfold pairLaw mixture
    rw [Measure.map_add _ _ measurable_swap, map_finsetSum _ _ measurable_swap]
    simp only [Measure.map_smul, Measure.prod_swap]
    congr 1
    unfold CouplingMixture.diagonal
    rw [Measure.map_map measurable_swap (show Measurable (fun x : ℝ => (x, x)) from
      measurable_id.prodMk measurable_id)]
    rfl
  let d : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (diagonalMass κ m a b t) +
    ∑ i, ENNReal.ofReal (componentProbabilities κ m a b t i) *
      ENNReal.ofReal (rightDensity m a b i x)
  have hpair : (baseLaw.withDensity d) ⊗ₘ leftGivenRight κ m a b t =
      (pairLaw κ m a b t).map Prod.swap := by
    unfold leftGivenRight d
    rw [diagonalReplacementKernel_disintegration _ _ hq]
    · rw [hswap]
      unfold CouplingMixture.diagonal
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [rightLaw_eq_withDensity (by linarith) ha0 ha' hb0 hb']
    · exact finite_total _ _ _
  have hfst := congrArg Measure.fst hpair
  rw [Measure.fst_compProd, Measure.fst_map_swap] at hfst
  rw [← hfst]
  exact hpair

end SourceParameters
end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleRepresentative
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.CocycleSupport

theorem measurePreserving_productRepresentative {ι : Type*} (i : ι) :
    MeasurePreserving
      (fun x : ι → UnitAddCircle => ((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ))
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))
      (volume.restrict (Ico (0 : ℝ) 1)) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  exact measurePreserving_circleRepresentative.comp
    (measurePreserving_eval_infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)) i)

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CocycleSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.CocycleSupport

theorem uniform_floor_ne_zero_le (t : ℝ) :
    (volume.restrict (Ico (0 : ℝ) 1)) {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ≤
      ENNReal.ofReal |t| := by
  have hm : MeasurableSet {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
    ((measurable_id.add_const t).floor (measurableSet_singleton 0)).compl
  rw [Measure.restrict_apply hm]
  rcases le_or_gt 0 t with ht | ht
  · calc
      volume ({x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ∩ Ico 0 1) ≤
          volume (Ico (1 - t) 1) := by
        apply measure_mono
        rintro x ⟨hx, hx0, hx1⟩
        refine ⟨?_, hx1⟩
        by_contra h
        apply hx
        apply Int.floor_eq_zero_iff.mpr
        constructor <;> linarith
      _ = ENNReal.ofReal |t| := by
        rw [Real.volume_Ico, abs_of_nonneg ht]
        congr 1
        ring
  · calc
      volume ({x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ∩ Ico 0 1) ≤
          volume (Ico 0 (-t)) := by
        apply measure_mono
        rintro x ⟨hx, hx0, hx1⟩
        refine ⟨hx0, ?_⟩
        by_contra h
        apply hx
        apply Int.floor_eq_zero_iff.mpr
        constructor <;> linarith
      _ = ENNReal.ofReal |t| := by
        rw [Real.volume_Ico, sub_zero, abs_of_neg ht]

theorem ae_finite_support_of_tsum_ne_top {Ω ι A : Type*}
    [MeasurableSpace Ω] [Countable ι] [Zero A]
    (μ : Measure Ω) (a : ι → Ω → A)
    (h : (∑' i, μ {x | a i x ≠ 0}) ≠ ∞) :
    ∀ᵐ x ∂μ, (Function.support (fun i => a i x)).Finite := by
  exact ae_finite_setOfPred_mem h

theorem ae_all_finite_support_of_tsum_ne_top {Ω ι K A : Type*}
    [MeasurableSpace Ω] [Countable ι] [Countable K] [Zero A]
    (μ : Measure Ω) (a : K → ι → Ω → A)
    (h : ∀ k, (∑' i, μ {x | a k i x ≠ 0}) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ k, (Function.support (fun i => a k i x)).Finite := by
  rw [ae_all_iff]
  intro k
  exact ae_finite_support_of_tsum_ne_top μ (a k) (h k)

theorem measure_floor_ne_zero_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (u : Ω → ℝ) (hu : Measurable u)
    (hlaw : μ.map u = volume.restrict (Ico (0 : ℝ) 1)) (t : ℝ) :
    μ {x | ⌊u x + t⌋ ≠ (0 : ℤ)} ≤ ENNReal.ofReal |t| := by
  have hm : MeasurableSet {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
    ((measurable_id.add_const t).floor (measurableSet_singleton 0)).compl
  calc
    μ {x | ⌊u x + t⌋ ≠ (0 : ℤ)} =
        (μ.map u) {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
      (Measure.map_apply hu hm).symm
    _ = (volume.restrict (Ico (0 : ℝ) 1))
        {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} := by rw [hlaw]
    _ ≤ ENNReal.ofReal |t| := uniform_floor_ne_zero_le t

theorem ae_all_int_finite_floor_support {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (u : ι → Ω → ℝ) (hu : ∀ i, Measurable (u i))
    (hlaw : ∀ i, μ.map (u i) = volume.restrict (Ico (0 : ℝ) 1))
    (θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂μ, ∀ k : ℤ,
      (Function.support (fun i => (⌊u i x + (k : ℝ) * θ i⌋ : ℤ))).Finite := by
  apply ae_all_finite_support_of_tsum_ne_top
  intro k
  apply ne_top_of_le_ne_top ((hθ.mul_left |(k : ℝ)|).tsum_ofReal_ne_top)
  apply ENNReal.tsum_le_tsum
  intro i
  simpa only [abs_mul, abs_of_nonneg (hθ0 i)] using
    measure_floor_ne_zero_le μ (u i) (hu i) (hlaw i) ((k : ℝ) * θ i)

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.CocycleSupport

theorem ae_product_all_int_finite_floor_support {ι : Type*} [Countable ι]
    (θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂(Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))),
      ∀ k : ℤ,
        (Function.support (fun i =>
          (⌊((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ) + (k : ℝ) * θ i⌋ : ℤ))).Finite := by
  exact ae_all_int_finite_floor_support
    (Ω := ι → UnitAddCircle) (ι := ι)
    (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))
    (fun i x => ((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ))
    (fun i => (measurePreserving_productRepresentative i).measurable)
    (fun i => (measurePreserving_productRepresentative i).map_eq)
    θ hθ0 hθ

end Invariant233.CocycleSupport

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
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function

namespace Invariant233.ProductCocycle

theorem representative_mem_Ico (x : UnitAddCircle) :
    representative x ∈ Ico (0 : ℝ) 1 := by
  simpa only [representative, zero_add] using (AddCircle.equivIco (1 : ℝ) 0 x).property

theorem cocycleVersion_ratio_le_one {I : Type*}
    (θ c : I → ℝ) (k : ℤ) (x y : Space I)
    (hc : ∀ i, 0 ≤ c i)
    (hxy : ∀ i, representative (x i) ≤ representative (y i))
    (hx : HasFiniteSupport
      (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋))
    (hy : HasFiniteSupport
      (fun i ↦ ⌊representative (y i) + (k : ℝ) * θ i⌋)) :
    cocycleVersion θ c k y / cocycleVersion θ c k x ≤ 1 :=
  FiniteSupportCocycle.exp_tsum_floor_ratio_le_one _ _ θ c k hc hxy hx hy

end Invariant233.ProductCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductConditionalAttenuation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Function Set
open scoped BigOperators

namespace Invariant233.ProductCocycle

theorem cocycleVersion_ratio_le_exp_of_crossing {ι : Type*}
    (θ c : ι → ℝ) (k : ℤ) (x y : Space ι) (i : ι)
    (hc : ∀ j, 0 ≤ c j)
    (horder : ∀ j, representative (x j) ≤ representative (y j))
    (hx : HasFiniteSupport (fun j => ⌊representative (x j) + (k : ℝ) * θ j⌋))
    (hy : HasFiniteSupport (fun j => ⌊representative (y j) + (k : ℝ) * θ j⌋))
    (hcross : representative (x i) < 1 - Int.fract ((k : ℝ) * θ i) ∧
      1 - Int.fract ((k : ℝ) * θ i) ≤ representative (y i)) :
    cocycleVersion θ c k y / cocycleVersion θ c k x ≤ Real.exp (-c i) := by
  classical
  have h := FiniteSupportCocycle.exp_tsum_floor_ratio_le_finite_crossings
    (fun j => representative (x j)) (fun j => representative (y j))
    (fun j => (k : ℝ) * θ j) c {i}
    (fun j => representative_mem_Ico (x j)) (fun j => representative_mem_Ico (y j))
    hc horder hx hy (by simpa using hcross)
  simpa only [cocycleVersion, Finset.sum_singleton] using h

theorem ae_all_int_finite_floor_support_of_map_ac
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (x : Ω → Space ι) (hx : AEMeasurable x μ) (hac : μ.map x ≪ haar ι) :
    ∀ᵐ ω ∂μ, ∀ k : ℤ,
      HasFiniteSupport (fun i => ⌊representative (x ω i) + (k : ℝ) * θ i⌋) := by
  apply ae_of_ae_map hx (p := fun z : Space ι => ∀ k : ℤ,
    HasFiniteSupport (fun i => ⌊representative (z i) + (k : ℝ) * θ i⌋))
  apply hac.ae_le
  exact CocycleSupport.ae_product_all_int_finite_floor_support θ hθ0 hθ

theorem ae_all_int_ratio_bounds_of_map_ac
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (θ c : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : Summable θ) (hc : ∀ i, 0 ≤ c i)
    (x y : Ω → Space ι) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hacx : μ.map x ≪ haar ι) (hacy : μ.map y ≪ haar ι)
    (horder : ∀ᵐ ω ∂μ, ∀ i, representative (x ω i) ≤ representative (y ω i)) :
    ∀ᵐ ω ∂μ, ∀ k : ℤ,
      cocycleVersion θ c k (y ω) / cocycleVersion θ c k (x ω) ≤ 1 ∧
      ∀ i, (representative (x ω i) < 1 - Int.fract ((k : ℝ) * θ i) ∧
        1 - Int.fract ((k : ℝ) * θ i) ≤ representative (y ω i)) →
      cocycleVersion θ c k (y ω) / cocycleVersion θ c k (x ω) ≤ Real.exp (-c i) := by
  filter_upwards [ae_all_int_finite_floor_support_of_map_ac μ θ hθ0 hθ x hx hacx,
    ae_all_int_finite_floor_support_of_map_ac μ θ hθ0 hθ y hy hacy, horder]
    with ω hxs hys hord
  intro k
  exact ⟨cocycleVersion_ratio_le_one θ c k (x ω) (y ω) hc hord (hxs k) (hys k),
    fun i hi => cocycleVersion_ratio_le_exp_of_crossing θ c k (x ω) (y ω) i
      hc hord (hxs k) (hys k) hi⟩

theorem finite_conditional_attenuation_of_map_ac
    {ι Ω : Type*} [Countable ι]
    (mx my : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (hmx : mx ≤ mΩ) (hmy : my ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (θ c : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (k : ℤ) (I : Finset ι)
    (x y : Ω → Space ι) (hx : Measurable[mx] x) (hy : Measurable[my] y)
    (hacx : μ.map x ≪ haar ι) (hacy : μ.map y ≪ haar ι)
    (top bottom : ι → Set Ω)
    (htop : ∀ i, MeasurableSet (top i)) (hbottom : ∀ i, MeasurableSet (bottom i))
    (hindTop : iCondIndepSet mx hmx top μ) (hindBottom : iCondIndepSet my hmy bottom μ)
    (m ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : L ≤ m * ρ)
    (hI : m / 20 ≤ (I.card : ℝ)) (hcost : ∀ i ∈ I, L ≤ c i)
    (horder : ∀ᵐ ω ∂μ, ∀ i, representative (x ω i) ≤ representative (y ω i))
    (hforceTop : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      representative (x ω i) < 1 - Int.fract ((k : ℝ) * θ i) →
      ω ∈ top i → 1 - Int.fract ((k : ℝ) * θ i) ≤ representative (y ω i))
    (hforceBottom : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      1 - Int.fract ((k : ℝ) * θ i) ≤ representative (y ω i) →
      ω ∈ bottom i → representative (x ω i) < 1 - Int.fract ((k : ℝ) * θ i))
    (hprobTop : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      representative (x ω i) < 1 - Int.fract ((k : ℝ) * θ i) →
      ρ / 10 ≤ (μ[(top i).indicator (fun _ => (1 : ℝ)) | mx]) ω)
    (hprobBottom : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      1 - Int.fract ((k : ℝ) * θ i) ≤ representative (y ω i) →
      ρ / 10 ≤ (μ[(bottom i).indicator (fun _ => (1 : ℝ)) | my]) ω) :
    ∃ H₁ H₂ : Set Ω, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂μ, (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂μ, (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂μ, cocycleVersion θ c k (y ω) / cocycleVersion θ c k (x ω) ≤
        Real.exp (-L) + H₁.indicator (fun _ => (1 : ℝ)) ω +
          H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  have hxrep : Measurable[mx] (fun ω i => representative (x ω i)) := by
    let : MeasurableSpace Ω := mx
    exact Measurable.of_eval (fun i => measurable_representative.comp ((measurable_pi_apply i).comp hx))
  have hyrep : Measurable[my] (fun ω i => representative (y ω i)) := by
    let : MeasurableSpace Ω := my
    exact Measurable.of_eval (fun i => measurable_representative.comp ((measurable_pi_apply i).comp hy))
  have hr := ae_all_int_ratio_bounds_of_map_ac μ θ c hθ0 hθ hc x y
    (hx.mono hmx le_rfl).aemeasurable (hy.mono hmy le_rfl).aemeasurable hacx hacy horder
  apply CrossingAvoidance.finite_conditional_attenuation mx my hmx hmy μ I
    (fun i => 1 - Int.fract ((k : ℝ) * θ i))
    (fun ω i => representative (x ω i)) (fun ω i => representative (y ω i))
    hxrep hyrep top bottom htop hbottom hindTop hindBottom m ρ L hρ hL hI
    (horder.mono (fun _ h i _ => h i)) hforceTop hforceBottom hprobTop hprobBottom
    (fun ω => cocycleVersion θ c k (y ω) / cocycleVersion θ c k (x ω))
    (hr.mono (fun _ h => (h k).1))
  filter_upwards [hr] with ω hω
  intro i hi hcross
  exact ((hω k).2 i hcross).trans (Real.exp_le_exp.mpr (neg_le_neg (hcost i hi)))

end Invariant233.ProductCocycle

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_IndependentKernelProduct
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Invariant233.KernelProduct

variable {ι : Type*} {A B : ι → Type*}
  [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]

theorem compProd_map_pairCoordinates (μ : ∀ i, Measure (A i))
    [∀ i, IsProbabilityMeasure (μ i)] (κ : ∀ i, Kernel (A i) (B i))
    [∀ i, IsMarkovKernel (κ i)] :
    ((Measure.infinitePi μ) ⊗ₘ independent κ).map pairCoordinates =
      Measure.infinitePi (fun i => μ i ⊗ₘ κ i) := by
  apply Measure.eq_infinitePi
  intro s t ht
  have hpair : Measurable (pairCoordinates (A := A) (B := B)) :=
    pairCoordinates.measurable
  have hset : MeasurableSet (Set.pi (s : Set ι) t) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ht i)
  rw [Measure.map_apply hpair hset, Measure.compProd_apply (hpair hset)]
  have hsection (x : ∀ i, A i) :
      Prod.mk x ⁻¹' (pairCoordinates ⁻¹' Set.pi (s : Set ι) t) =
        Set.pi (s : Set ι) (fun i => Prod.mk (x i) ⁻¹' t i) := by
    ext y
    rfl
  simp_rw [hsection, independent_apply,
    Measure.infinitePi_pi _ (fun i _ => measurable_prodMk_left (ht i))]
  have hg (i : ι) : Measurable (fun a : A i => κ i a (Prod.mk a ⁻¹' t i)) :=
    Kernel.measurable_kernel_prodMk_left (ht i)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun (μ := Measure.infinitePi μ) s
    (fun i (x : ∀ i, A i) => κ i (x i) (Prod.mk (x i) ⁻¹' t i))
    (iIndepFun_infinitePi hg) (fun i => (hg i).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [Measure.compProd_apply (ht i)]
  exact (measurePreserving_eval_infinitePi μ i).lintegral_comp (hg i)

end Invariant233.KernelProduct

namespace Invariant233.KernelProduct
variable {ι : Type*} {X A B : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (A i)]
  [∀ i, MeasurableSpace (B i)]

theorem coordinate_pair_disintegration (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (obs : ∀ i, X i → A i)
    (val : ∀ i, X i → B i) (hobs : ∀ i, Measurable (obs i))
    (hval : ∀ i, Measurable (val i)) (κ : ∀ i, Kernel (A i) (B i))
    [∀ i, IsMarkovKernel (κ i)]
    (hκ : ∀ i, (μ i).map (obs i) ⊗ₘ κ i =
      (μ i).map (fun z => (obs i z, val i z))) :
    ((Measure.infinitePi μ).map (fun z i => obs i (z i))) ⊗ₘ independent κ =
      (Measure.infinitePi μ).map
        (fun z => (fun i => obs i (z i), fun i => val i (z i))) := by
  let (index : ι) : IsProbabilityMeasure ((μ index).map (obs index)) := Measure.isProbabilityMeasure_map (hobs index).aemeasurable
  apply (pairCoordinates (A := A) (B := B)).map_measurableEquiv_injective
  rw [Measure.infinitePi_map_pi μ hobs, compProd_map_pairCoordinates]
  rw [Measure.map_map pairCoordinates.measurable (by fun_prop)]
  change Measure.infinitePi (fun i => (μ i).map (obs i) ⊗ₘ κ i) =
    (Measure.infinitePi μ).map (fun z i => (obs i (z i), val i (z i)))
  rw [Measure.infinitePi_map_pi μ (f := fun i z => (obs i z, val i z))
    (fun i => (hobs i).prodMk (hval i))]
  congr 1
  funext i
  exact hκ i

variable [Countable ι] [∀ i, StandardBorelSpace (B i)] [∀ i, Nonempty (B i)]

theorem condDistrib_of_coordinate_disintegration (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (obs : ∀ i, X i → A i)
    (val : ∀ i, X i → B i) (hobs : ∀ i, Measurable (obs i))
    (hval : ∀ i, Measurable (val i)) (κ : ∀ i, Kernel (A i) (B i))
    [∀ i, IsMarkovKernel (κ i)]
    (hκ : ∀ i, (μ i).map (obs i) ⊗ₘ κ i =
      (μ i).map (fun z => (obs i z, val i z))) :
    condDistrib (fun z i => val i (z i)) (fun z i => obs i (z i))
      (Measure.infinitePi μ)
      =ᵐ[(Measure.infinitePi μ).map (fun z i => obs i (z i))] independent κ := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (by fun_prop) (by fun_prop)
  exact (coordinate_pair_disintegration μ obs val hobs hval κ hκ).symm

end Invariant233.KernelProduct

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductConditionalKernels
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Invariant233.OrderedProductCoupling
open OneCoordinateCoupling KernelProduct

private lemma coordinate_right_disintegration (P : Parameters) (i : ℕ) :
    (coordinateLaw P i).map (fun z => z.2.1) ⊗ₘ
      rightGivenLeft (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i) =
        (coordinateLaw P i).map (fun z => (z.2.1, z.2.2)) := by
  have hleft : (coordinateLaw P i).map (fun z => z.2.1) =
      (pairLaw (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)).fst := by
    rw [← coordinateLaw_map_pair P i, Measure.fst,
      Measure.map_map measurable_fst measurable_snd]
    rfl
  rw [hleft]
  simpa only [Prod.eta] using
    (rightGivenLeft_disintegration (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
      (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)).trans (coordinateLaw_map_pair P i).symm

private lemma coordinate_left_disintegration (P : Parameters) (i : ℕ) :
    (coordinateLaw P i).map (fun z => z.2.2) ⊗ₘ
      leftGivenRight (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i) =
        (coordinateLaw P i).map (fun z => (z.2.2, z.2.1)) := by
  have hright : (coordinateLaw P i).map (fun z => z.2.2) =
      (pairLaw (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)).snd := by
    rw [← coordinateLaw_map_pair P i, Measure.snd,
      Measure.map_map measurable_snd measurable_snd]
    rfl
  rw [hright, leftGivenRight_disintegration (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
    (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
    (P.t_nonneg i) (P.t_le i), ← coordinateLaw_map_pair P i,
    Measure.map_map measurable_swap measurable_snd]
  rfl

theorem right_condDistrib_eq_product (P : Parameters) :
    condDistrib rightEndpoint leftEndpoint (law P)
      =ᵐ[(law P).map leftEndpoint] fun x => Measure.infinitePi
        (fun i => rightGivenLeft (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i) (x i)) := by
  let (i : ℕ) : IsMarkovKernel
      (rightGivenLeft (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)) :=
    rightGivenLeft_isMarkov (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
      (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)
  exact condDistrib_of_coordinate_disintegration (coordinateLaw P)
    (fun _ z => z.2.1) (fun _ z => z.2.2) (by fun_prop) (by fun_prop)
    (fun i => rightGivenLeft (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i))
    (coordinate_right_disintegration P)

theorem left_condDistrib_eq_product (P : Parameters) :
    condDistrib leftEndpoint rightEndpoint (law P)
      =ᵐ[(law P).map rightEndpoint] fun y => Measure.infinitePi
        (fun i => leftGivenRight (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i) (y i)) := by
  let (i : ℕ) : IsMarkovKernel
      (leftGivenRight (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)) :=
    leftGivenRight_isMarkov (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
      (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)
  exact condDistrib_of_coordinate_disintegration (coordinateLaw P)
    (fun _ z => z.2.2) (fun _ z => z.2.1) (by fun_prop) (by fun_prop)
    (fun i => leftGivenRight (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i))
    (coordinate_left_disintegration P)

theorem right_coordinates_conditionally_independent (P : Parameters) :
    ∀ᵐ x ∂(law P).map leftEndpoint,
      iIndepFun (fun i (y : Endpoint) => y i)
        (condDistrib rightEndpoint leftEndpoint (law P) x) := by
  let (i : ℕ) : IsMarkovKernel
      (rightGivenLeft (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)) :=
    rightGivenLeft_isMarkov (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
      (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)
  filter_upwards [right_condDistrib_eq_product P] with x hx
  rw [hx]
  exact iIndepFun_infinitePi (fun _ => measurable_id)

theorem left_coordinates_conditionally_independent (P : Parameters) :
    ∀ᵐ y ∂(law P).map rightEndpoint,
      iIndepFun (fun i (x : Endpoint) => x i)
        (condDistrib leftEndpoint rightEndpoint (law P) y) := by
  let (i : ℕ) : IsMarkovKernel
      (leftGivenRight (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)) :=
    leftGivenRight_isMarkov (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
      (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)
  filter_upwards [left_condDistrib_eq_product P] with y hy
  rw [hy]
  exact iIndepFun_infinitePi (fun _ => measurable_id)

theorem right_condDistrib_coordinate_law (P : Parameters) :
    ∀ᵐ x ∂(law P).map leftEndpoint, ∀ i,
      (condDistrib rightEndpoint leftEndpoint (law P) x).map
        (fun y : Endpoint => y i) =
      rightGivenLeft (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i) (x i) := by
  let (i : ℕ) : IsMarkovKernel
      (rightGivenLeft (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)) :=
    rightGivenLeft_isMarkov (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
      (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)
  filter_upwards [right_condDistrib_eq_product P] with x hx i
  rw [hx, Measure.infinitePi_map_eval]

theorem left_condDistrib_coordinate_law (P : Parameters) :
    ∀ᵐ y ∂(law P).map rightEndpoint, ∀ i,
      (condDistrib leftEndpoint rightEndpoint (law P) y).map
        (fun x : Endpoint => x i) =
      leftGivenRight (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i) (y i) := by
  let (i : ℕ) : IsMarkovKernel
      (leftGivenRight (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)) :=
    leftGivenRight_isMarkov (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
      (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)
  filter_upwards [left_condDistrib_eq_product P] with y hy i
  rw [hy, Measure.infinitePi_map_eval]

theorem ae_leftEndpoint_mem_unit (P : Parameters) :
    ∀ᵐ x ∂(law P).map leftEndpoint, ∀ i, x i ∈ Set.Ico (0 : ℝ) 1 := by
  apply (ae_map_iff leftEndpoint_measurable.aemeasurable (by measurability)).mpr
  apply ae_all_iff.mpr
  intro i
  have hc : ∀ᵐ z ∂coordinateLaw P i, z.2.1 ∈ Set.Ico (0 : ℝ) 1 := by
    apply ae_of_ae_map ((measurable_fst.comp measurable_snd).aemeasurable)
    simp only [Function.comp_def]
    rw [coordinateLaw_map_left P i]
    exact (withDensity_absolutelyContinuous _ _).ae_le (CouplingMixture.intervalLaw_ae_mem 0 1)
  exact (measurePreserving_eval_infinitePi (coordinateLaw P) i).quasiMeasurePreserving.ae hc

theorem ae_rightEndpoint_mem_unit (P : Parameters) :
    ∀ᵐ y ∂(law P).map rightEndpoint, ∀ i, y i ∈ Set.Ico (0 : ℝ) 1 := by
  apply (ae_map_iff rightEndpoint_measurable.aemeasurable (by measurability)).mpr
  apply ae_all_iff.mpr
  intro i
  have hc : ∀ᵐ z ∂coordinateLaw P i, z.2.2 ∈ Set.Ico (0 : ℝ) 1 := by
    apply ae_of_ae_map ((measurable_snd.comp measurable_snd).aemeasurable)
    simp only [Function.comp_def]
    rw [coordinateLaw_map_right P i]
    exact (withDensity_absolutelyContinuous _ _).ae_le (CouplingMixture.intervalLaw_ae_mem 0 1)
  exact (measurePreserving_eval_infinitePi (coordinateLaw P) i).quasiMeasurePreserving.ae hc

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_OneCoordinateCrossing
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
namespace Invariant233.OneCoordinateCoupling
open CouplingMarginalBounds CouplingMixture FiniteKernelMixture

private lemma ofReal_total {I : Type*} [Fintype I] (q : ℝ) (p u : I → ℝ)
    (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i) (hu : ∀ i, 0 ≤ u i) :
    ENNReal.ofReal q + ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (u i) =
      ENNReal.ofReal (q + ∑ i, p i * u i) := by
  rw [ENNReal.ofReal_add hq (Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (hu i))),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hp i) (hu i))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (ENNReal.ofReal_mul (hp i)).symm

lemma intervalDensity_ge_one {a b x : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hab : a < b) (hx : x ∈ Ico a b) : 1 ≤ intervalDensity a b x := by
  rw [intervalDensity, uniformDensity, Set.indicator_of_mem hx,
    baseLaw_interval_measure ha hb hab.le]
  exact (one_le_inv₀ (sub_pos.mpr hab)).mpr (by linarith)

lemma intervalLaw_Ici_eq_one {a b u : ℝ} (hab : a < b) (hu : u ≤ a) :
    intervalLaw a b (Ici u) = 1 := by
  let := intervalLaw_isProbabilityMeasure hab
  apply (mem_ae_iff_prob_eq_one measurableSet_Ici).mp
  filter_upwards [intervalLaw_ae_mem a b] with z hz
  exact hu.trans hz.1

lemma intervalLaw_Iio_eq_one {a b u : ℝ} (hab : a < b) (hu : b ≤ u) :
    intervalLaw a b (Iio u) = 1 := by
  let := intervalLaw_isProbabilityMeasure hab
  apply (mem_ae_iff_prob_eq_one measurableSet_Iio).mp
  filter_upwards [intervalLaw_ae_mem a b] with z hz
  exact hz.2.trans_le hu

section SourceParameters
variable {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)
include hκ0 hκ hm ha ha' hb hb' ht0 ht

lemma rightGivenLeft_component_lower (x : ℝ) (s : Set ℝ) (i : Fin 5)
    (hd : 1 ≤ leftDensity m a b i x) (hs : rightLaw m a b i s = 1) :
    ENNReal.ofReal (componentProbabilities κ m a b t i) / 10 ≤
      rightGivenLeft κ m a b t x s := by
  unfold rightGivenLeft
  apply diagonalReplacementKernel_event_lower _ _ _ _ _ x s i 10
  · exact ENNReal.one_le_ofReal.mpr hd
  · have hq := (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
    rw [ofReal_total _ _ _ (by linarith : 0 ≤ diagonalMass κ m a b t)
      (componentProbabilities_nonneg hκ0 (by linarith) ht0)
      (fun i => by fin_cases i <;> exact intervalDensity_nonneg _ _ _)]
    have hle := (leftMarginalDensity_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht x).2.2.le
    simpa only [leftMarginalDensity, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hle
  · exact hs

lemma leftGivenRight_component_lower (y : ℝ) (s : Set ℝ) (i : Fin 5)
    (hd : 1 ≤ rightDensity m a b i y) (hs : leftLaw m a b i s = 1) :
    ENNReal.ofReal (componentProbabilities κ m a b t i) / 10 ≤
      leftGivenRight κ m a b t y s := by
  unfold leftGivenRight
  apply diagonalReplacementKernel_event_lower _ _ _ _ _ y s i 10
  · exact ENNReal.one_le_ofReal.mpr hd
  · have hq := (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
    rw [ofReal_total _ _ _ (by linarith : 0 ≤ diagonalMass κ m a b t)
      (componentProbabilities_nonneg hκ0 (by linarith) ht0)
      (fun i => by fin_cases i <;> exact intervalDensity_nonneg _ _ _)]
    have hle := (rightMarginalDensity_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht y).2.2.le
    simpa only [rightMarginalDensity, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hle
  · exact hs

theorem rightGivenLeft_crossing_lower {w x u : ℝ} (hw : w = a ∨ w = b)
    (hx0 : 0 ≤ x) (hxu : x < u) (hu : u ≤ 1 - w) :
    ENNReal.ofReal (rho κ m w) / 10 ≤ rightGivenLeft κ m a b t x (Ici u) := by
  have ha0 := width_pos (by linarith : 0 < m) ha
  have hb0 := width_pos (by linarith : 0 < m) hb
  rcases hw with hw | hw
  · subst w
    have hd : 1 ≤ leftDensity m a b 0 x := by
      change 1 ≤ intervalDensity 0 (1 - a / 2) x
      apply intervalDensity_ge_one (by norm_num) (by linarith) (by linarith)
      exact ⟨hx0, by linarith⟩
    have hs : rightLaw m a b 0 (Ici u) = 1 := by
      change intervalLaw (1 - a / 2) 1 (Ici u) = 1
      exact intervalLaw_Ici_eq_one (by linarith) (by linarith)
    exact rightGivenLeft_component_lower hκ0 hκ hm ha ha' hb hb' ht0 ht x (Ici u) 0 hd hs
  · subst w
    have hd : 1 ≤ leftDensity m a b 2 x := by
      change 1 ≤ intervalDensity 0 (1 - b / 2) x
      apply intervalDensity_ge_one (by norm_num) (by linarith) (by linarith)
      exact ⟨hx0, by linarith⟩
    have hs : rightLaw m a b 2 (Ici u) = 1 := by
      change intervalLaw (1 - b / 2) 1 (Ici u) = 1
      exact intervalLaw_Ici_eq_one (by linarith) (by linarith)
    exact rightGivenLeft_component_lower hκ0 hκ hm ha ha' hb hb' ht0 ht x (Ici u) 2 hd hs

theorem leftGivenRight_crossing_lower {w y u : ℝ} (hw : w = a ∨ w = b)
    (hy1 : y < 1) (huy : u ≤ y) (hu : w ≤ u) :
    ENNReal.ofReal (rho κ m w) / 10 ≤ leftGivenRight κ m a b t y (Iio u) := by
  have ha0 := width_pos (by linarith : 0 < m) ha
  have hb0 := width_pos (by linarith : 0 < m) hb
  rcases hw with hw | hw
  · subst w
    have hd : 1 ≤ rightDensity m a b 1 y := by
      change 1 ≤ intervalDensity (a / 2) 1 y
      apply intervalDensity_ge_one (by linarith) (by norm_num) (by linarith)
      exact ⟨by linarith, hy1⟩
    have hs : leftLaw m a b 1 (Iio u) = 1 := by
      change intervalLaw 0 (a / 2) (Iio u) = 1
      exact intervalLaw_Iio_eq_one (by linarith) (by linarith)
    exact leftGivenRight_component_lower hκ0 hκ hm ha ha' hb hb' ht0 ht y (Iio u) 1 hd hs
  · subst w
    have hd : 1 ≤ rightDensity m a b 3 y := by
      change 1 ≤ intervalDensity (b / 2) 1 y
      apply intervalDensity_ge_one (by linarith) (by norm_num) (by linarith)
      exact ⟨by linarith, hy1⟩
    have hs : leftLaw m a b 3 (Iio u) = 1 := by
      change intervalLaw 0 (b / 2) (Iio u) = 1
      exact intervalLaw_Iio_eq_one (by linarith) (by linarith)
    exact leftGivenRight_component_lower hκ0 hκ hm ha ha' hb hb' ht0 ht y (Iio u) 3 hd hs

end SourceParameters
end Invariant233.OneCoordinateCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductConditionalCrossing
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.flatten_unflatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Invariant233.OrderedProductCoupling
open OneCoordinateCoupling CouplingMarginalBounds

theorem right_condDistrib_crossing_lower (P : Parameters) :
    ∀ᵐ x ∂(law P).map leftEndpoint, ∀ (i : ℕ) (w u : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u → u ≤ 1 - w → x i < u →
      ENNReal.ofReal (rho (P.κ i) (P.m i) w) / 10 ≤
        condDistrib rightEndpoint leftEndpoint (law P) x
          {y : Endpoint | x i < u ∧ u ≤ y i} := by
  filter_upwards [right_condDistrib_coordinate_law P, ae_leftEndpoint_mem_unit P]
    with x hx hxunit i w u hw _hu0 hu1 hxu
  have hevent : {y : Endpoint | x i < u ∧ u ≤ y i} =
      (fun y : Endpoint => y i) ⁻¹' Ici u := by
    ext y
    simp [hxu]
  rw [hevent, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Ici, hx i]
  exact rightGivenLeft_crossing_lower (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
    (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
    (P.t_nonneg i) (P.t_le i) hw (hxunit i).1 hxu hu1

theorem left_condDistrib_crossing_lower (P : Parameters) :
    ∀ᵐ y ∂(law P).map rightEndpoint, ∀ (i : ℕ) (w u : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u → u ≤ 1 - w → u ≤ y i →
      ENNReal.ofReal (rho (P.κ i) (P.m i) w) / 10 ≤
        condDistrib leftEndpoint rightEndpoint (law P) y
          {x : Endpoint | x i < u ∧ u ≤ y i} := by
  filter_upwards [left_condDistrib_coordinate_law P, ae_rightEndpoint_mem_unit P]
    with y hy hyunit i w u hw hu0 _hu1 huy
  have hevent : {x : Endpoint | x i < u ∧ u ≤ y i} =
      (fun x : Endpoint => x i) ⁻¹' Iio u := by
    ext x
    simp [huy]
  rw [hevent, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Iio, hy i]
  exact leftGivenRight_crossing_lower (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
    (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
    (P.t_nonneg i) (P.t_le i) hw (hyunit i).2 huy hu0

theorem right_condDistrib_crossing_real_lower (P : Parameters) :
    ∀ᵐ x ∂(law P).map leftEndpoint, ∀ (i : ℕ) (w u : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u → u ≤ 1 - w → x i < u →
      rho (P.κ i) (P.m i) w / 10 ≤
        (condDistrib rightEndpoint leftEndpoint (law P) x).real
          {y : Endpoint | x i < u ∧ u ≤ y i} := by
  filter_upwards [right_condDistrib_crossing_lower P] with x hx i w u hw hu0 hu1 hxu
  have h := ENNReal.toReal_mono (measure_ne_top _ _) (hx i w u hw hu0 hu1 hxu)
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofReal (rho_nonneg (P.κ_nonneg i)),
    ENNReal.toReal_ofNat, measureReal_def] using h

theorem left_condDistrib_crossing_real_lower (P : Parameters) :
    ∀ᵐ y ∂(law P).map rightEndpoint, ∀ (i : ℕ) (w u : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u → u ≤ 1 - w → u ≤ y i →
      rho (P.κ i) (P.m i) w / 10 ≤
        (condDistrib leftEndpoint rightEndpoint (law P) y).real
          {x : Endpoint | x i < u ∧ u ≤ y i} := by
  filter_upwards [left_condDistrib_crossing_lower P] with y hy i w u hw hu0 hu1 huy
  have h := ENNReal.toReal_mono (measure_ne_top _ _) (hy i w u hw hu0 hu1 huy)
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofReal (rho_nonneg (P.κ_nonneg i)),
    ENNReal.toReal_ofNat, measureReal_def] using h

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductConditionalEvents
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Invariant233.OrderedProductCoupling

theorem right_thresholds_iCondIndepSet (P : Parameters) (u : ℕ → ℝ) :
    iCondIndepSet (MeasurableSpace.comap leftEndpoint inferInstance)
      leftEndpoint_measurable.comap_le
      (fun i => {ω : Sample | u i ≤ rightEndpoint ω i}) (law P) := by
  apply ConditionalEventBridge.iCondIndepSet_preimage_of_condDistrib
    (law P) leftEndpoint rightEndpoint leftEndpoint_measurable rightEndpoint_measurable
    (fun i => {y : Endpoint | u i ≤ y i})
    (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  filter_upwards [right_coordinates_conditionally_independent P] with x hx
  apply (iIndepSet_iff_meas_biInter
    (fun i => measurableSet_le measurable_const (measurable_pi_apply i))).2
  intro S
  exact hx.meas_biInter (fun i _ =>
    ⟨Ici (u i), measurableSet_Ici, rfl⟩)

theorem left_thresholds_iCondIndepSet (P : Parameters) (u : ℕ → ℝ) :
    iCondIndepSet (MeasurableSpace.comap rightEndpoint inferInstance)
      rightEndpoint_measurable.comap_le
      (fun i => {ω : Sample | leftEndpoint ω i < u i}) (law P) := by
  apply ConditionalEventBridge.iCondIndepSet_preimage_of_condDistrib
    (law P) rightEndpoint leftEndpoint rightEndpoint_measurable leftEndpoint_measurable
    (fun i => {x : Endpoint | x i < u i})
    (fun i => measurableSet_lt (measurable_pi_apply i) measurable_const)
  filter_upwards [left_coordinates_conditionally_independent P] with y hy
  apply (iIndepSet_iff_meas_biInter
    (fun i => measurableSet_lt (measurable_pi_apply i) measurable_const)).2
  intro S
  exact hy.meas_biInter (fun i _ =>
    ⟨Iio (u i), measurableSet_Iio, rfl⟩)

theorem right_threshold_condExp_lower (P : Parameters) (u : ℕ → ℝ) :
    ∀ᵐ ω ∂law P, ∀ (i : ℕ) (w : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u i → u i ≤ 1 - w →
      leftEndpoint ω i < u i →
      CouplingMarginalBounds.rho (P.κ i) (P.m i) w / 10 ≤
        ((law P)[{ω : Sample | u i ≤ rightEndpoint ω i}.indicator
          (fun _ => (1 : ℝ)) | MeasurableSpace.comap leftEndpoint inferInstance]) ω := by
  have heq : ∀ᵐ ω ∂law P, ∀ i,
      (condDistrib rightEndpoint leftEndpoint (law P) (leftEndpoint ω)).real
        {y : Endpoint | u i ≤ y i} =
      ((law P)[{ω : Sample | u i ≤ rightEndpoint ω i}.indicator
        (fun _ => (1 : ℝ)) | MeasurableSpace.comap leftEndpoint inferInstance]) ω :=
    ae_all_iff.mpr (fun i => condDistrib_ae_eq_condExp
      leftEndpoint_measurable rightEndpoint_measurable
      (measurableSet_le measurable_const (measurable_pi_apply i)))
  have hcross := ae_of_ae_map leftEndpoint_measurable.aemeasurable
    (right_condDistrib_crossing_real_lower P)
  filter_upwards [heq, hcross] with ω heq hcross i w hw hwu huw hxu
  rw [← heq i]
  simpa only [hxu, true_and] using hcross i w (u i) hw hwu huw hxu

theorem left_threshold_condExp_lower (P : Parameters) (u : ℕ → ℝ) :
    ∀ᵐ ω ∂law P, ∀ (i : ℕ) (w : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u i → u i ≤ 1 - w →
      u i ≤ rightEndpoint ω i →
      CouplingMarginalBounds.rho (P.κ i) (P.m i) w / 10 ≤
        ((law P)[{ω : Sample | leftEndpoint ω i < u i}.indicator
          (fun _ => (1 : ℝ)) | MeasurableSpace.comap rightEndpoint inferInstance]) ω := by
  have heq : ∀ᵐ ω ∂law P, ∀ i,
      (condDistrib leftEndpoint rightEndpoint (law P) (rightEndpoint ω)).real
        {x : Endpoint | x i < u i} =
      ((law P)[{ω : Sample | leftEndpoint ω i < u i}.indicator
        (fun _ => (1 : ℝ)) | MeasurableSpace.comap rightEndpoint inferInstance]) ω :=
    ae_all_iff.mpr (fun i => condDistrib_ae_eq_condExp
      rightEndpoint_measurable leftEndpoint_measurable
      (measurableSet_lt (measurable_pi_apply i) measurable_const))
  have hcross := ae_of_ae_map rightEndpoint_measurable.aemeasurable
    (left_condDistrib_crossing_real_lower P)
  filter_upwards [heq, hcross] with ω heq hcross i w hw hwu huw huy
  rw [← heq i]
  simpa only [huy, and_true] using hcross i w (u i) hw hwu huw huy

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductCouplingCircle
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Invariant233.OrderedProductCoupling

open OneCoordinateCoupling

lemma baseLaw_eq_restrict : baseLaw = volume.restrict (Ico (0 : ℝ) 1) := by
  simp [baseLaw, CouplingMixture.intervalLaw, ProbabilityTheory.cond, Real.volume_Ico]

lemma realEndpoint_measurable : Measurable realEndpoint := by
  apply Measurable.of_eval
  intro i
  exact (CocycleSupport.measurePreserving_circleRepresentative.measurable).comp
    (measurable_pi_apply i)

lemma measurePreserving_circleQuotient :
    MeasurePreserving (fun x : ℝ => (x : Circle)) baseLaw circleMeasure := by
  rw [baseLaw_eq_restrict]
  change MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
    (volume.restrict (Ico 0 1)) volume
  rw [restrict_Ico_eq_restrict_Ioc]
  simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0

lemma measurePreserving_circleEndpoint :
    MeasurePreserving circleEndpoint baseMeasure ProductModel.baseMeasure := by
  refine ⟨circleEndpoint_measurable, ?_⟩
  change (Measure.infinitePi (fun _ : ℕ => baseLaw)).map
    (fun x i => (x i : Circle)) = Measure.infinitePi (fun _ : ℕ => circleMeasure)
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => baseLaw)
    (fun _ => measurePreserving_circleQuotient.measurable)]
  simp_rw [measurePreserving_circleQuotient.map_eq]

lemma measurePreserving_realEndpoint :
    MeasurePreserving realEndpoint ProductModel.baseMeasure baseMeasure := by
  refine ⟨realEndpoint_measurable, ?_⟩
  change (Measure.infinitePi (fun _ : ℕ => circleMeasure)).map
    (fun x i => circleRepresentative (x i)) = Measure.infinitePi (fun _ : ℕ => baseLaw)
  unfold circleRepresentative
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => circleMeasure)
    (fun _ => CocycleSupport.measurePreserving_circleRepresentative.measurable)]
  congr 1
  funext i
  exact CocycleSupport.measurePreserving_circleRepresentative.map_eq.trans
    baseLaw_eq_restrict.symm

lemma circleEndpoint_realEndpoint (x : ProductModel.Base) :
    circleEndpoint (realEndpoint x) = x := by
  funext i
  exact AddCircle.coe_equivIco

lemma realEndpoint_circleEndpoint_of_mem {x : Endpoint}
    (hx : ∀ i, x i ∈ Ico (0 : ℝ) 1) : realEndpoint (circleEndpoint x) = x := by
  funext i
  exact AddCircle.equivIco_coe_of_mem (by simpa using hx i)

lemma ae_realEndpoint_circleEndpoint :
    ∀ᵐ x ∂baseMeasure, realEndpoint (circleEndpoint x) = x := by
  have h : ∀ᵐ x ∂baseMeasure, ∀ i, x i ∈ Ico (0 : ℝ) 1 := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => baseLaw) i).quasiMeasurePreserving.ae
      (CouplingMixture.intervalLaw_ae_mem 0 1)
  exact h.mono (fun _ hx => realEndpoint_circleEndpoint_of_mem hx)

theorem circle_density_transport {g : Endpoint → ℝ} (hg : MemLp g 2 baseMeasure) :
    (baseMeasure.withDensity (fun x => ENNReal.ofReal (g x))).map circleEndpoint =
      ProductModel.baseMeasure.withDensity
        (fun x => ENNReal.ofReal (g (realEndpoint x))) ∧
      eLpNorm (g ∘ realEndpoint) 2 ProductModel.baseMeasure = eLpNorm g 2 baseMeasure :=
  DensityTransport.real_density_transport_ae circleEndpoint_measurable realEndpoint_measurable
    measurePreserving_circleEndpoint.map_eq ae_realEndpoint_circleEndpoint hg.aemeasurable

theorem exists_circle_hybrid_density (P : Parameters) (ε : ℕ → Bool) {C : ℝ}
    (hsum : Summable (energyBound P)) (hC : (∑' i, energyBound P i) ≤ C) :
    ∃ G : ProductModel.Base → ℝ,
      MemLp G 2 ProductModel.baseMeasure ∧ (0 ≤ᵐ[ProductModel.baseMeasure] G) ∧
      (∫ x, G x ∂ProductModel.baseMeasure) = 1 ∧
      eLpNorm G 2 ProductModel.baseMeasure ≤ ENNReal.ofReal (Real.exp (C / 2)) ∧
      (law P).map (circleHybridEndpoint ε) =
        ProductModel.baseMeasure.withDensity (fun x => ENNReal.ofReal (G x)) := by
  obtain ⟨g, hg, hn, hm, hnorm, hlaw⟩ := exists_hybrid_density P ε hsum hC
  have ht := circle_density_transport hg
  refine ⟨g ∘ realEndpoint, hg.comp_measurePreserving measurePreserving_realEndpoint,
    measurePreserving_realEndpoint.quasiMeasurePreserving.ae hn, ?_, ht.2.trans_le hnorm, ?_⟩
  · have hi := integral_map realEndpoint_measurable.aemeasurable
      (show AEStronglyMeasurable g (ProductModel.baseMeasure.map realEndpoint) by
        rw [measurePreserving_realEndpoint.map_eq]
        exact hg.aestronglyMeasurable)
    rw [measurePreserving_realEndpoint.map_eq] at hi
    exact hi.symm.trans hm
  · change (law P).map (circleEndpoint ∘ hybridEndpoint ε) = _
    rw [← Measure.map_map circleEndpoint_measurable (hybridEndpoint_measurable ε), hlaw]
    exact ht.1

theorem leftEndpoint_ae_mem_unit (P : Parameters) :
    ∀ᵐ ω ∂law P, ∀ i, leftEndpoint ω i ∈ Ico (0 : ℝ) 1 := by
  apply ae_all_iff.2
  intro i
  have hc : ∀ᵐ z ∂coordinateLaw P i, z.2.1 ∈ Ico (0 : ℝ) 1 := by
    apply (ae_map_iff (measurable_fst.comp measurable_snd).aemeasurable measurableSet_Ico).1
    change ∀ᵐ x ∂(coordinateLaw P i).map (fun z => z.2.1), x ∈ Ico (0 : ℝ) 1
    rw [coordinateLaw_map_left]
    exact (withDensity_absolutelyContinuous _ _).ae_le (CouplingMixture.intervalLaw_ae_mem 0 1)
  exact (measurePreserving_eval_infinitePi (coordinateLaw P) i).quasiMeasurePreserving.ae hc

theorem rightEndpoint_ae_mem_unit (P : Parameters) :
    ∀ᵐ ω ∂law P, ∀ i, rightEndpoint ω i ∈ Ico (0 : ℝ) 1 := by
  apply ae_all_iff.2
  intro i
  have hc : ∀ᵐ z ∂coordinateLaw P i, z.2.2 ∈ Ico (0 : ℝ) 1 := by
    apply (ae_map_iff (measurable_snd.comp measurable_snd).aemeasurable measurableSet_Ico).1
    change ∀ᵐ x ∂(coordinateLaw P i).map (fun z => z.2.2), x ∈ Ico (0 : ℝ) 1
    rw [coordinateLaw_map_right]
    exact (withDensity_absolutelyContinuous _ _).ae_le (CouplingMixture.intervalLaw_ae_mem 0 1)
  exact (measurePreserving_eval_infinitePi (coordinateLaw P) i).quasiMeasurePreserving.ae hc

theorem ae_real_circle_endpoints (P : Parameters) :
    ∀ᵐ ω ∂law P, realEndpoint (circleLeftEndpoint ω) = leftEndpoint ω ∧
      realEndpoint (circleRightEndpoint ω) = rightEndpoint ω := by
  filter_upwards [leftEndpoint_ae_mem_unit P, rightEndpoint_ae_mem_unit P] with ω hx hy
  exact ⟨realEndpoint_circleEndpoint_of_mem hx, realEndpoint_circleEndpoint_of_mem hy⟩

theorem ae_circle_endpoints_ordered (P : Parameters) :
    ∀ᵐ ω ∂law P, ProductModel.Ordered (circleLeftEndpoint ω) (circleRightEndpoint ω) := by
  filter_upwards [ae_real_circle_endpoints P, ae_ordered P] with ω hrep hord
  change realEndpoint (circleLeftEndpoint ω) ≤ realEndpoint (circleRightEndpoint ω)
  rw [hrep.1, hrep.2]
  exact hord

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductCouplingCircleSource
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace Invariant233.OrderedProductCoupling

theorem exists_source_circle_hybrid_density
    (m : ℕ → ℕ) (a b : ℕ → ℝ) (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (tag : ℕ) (ε : ℕ → Bool) :
    ∃ H : ProductModel.Base → ℝ, MemLp H 2 ProductModel.baseMeasure ∧
      (0 ≤ᵐ[ProductModel.baseMeasure] H) ∧
      (∫ x, H x ∂ProductModel.baseMeasure) = 1 ∧
      eLpNorm H 2 ProductModel.baseMeasure ≤ ENNReal.ofReal (blockDensityBound sourceKappa) ∧
      (law (ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm
        ha ha' hb hb' e tag)).map (circleHybridEndpoint ε) =
        ProductModel.baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) := by
  obtain ⟨hs, htotal⟩ := ofBlocks_energy_sum m sourceKappa a b
    sourceKappa_nonneg sourceKappa_le hm ha ha' hb hb' e tag summable_sourceKappa_sq
  have hbound : Real.exp ((20 * (2 * (∑' s, sourceKappa s ^ 2) + 1)) / 2) =
      blockDensityBound sourceKappa := by
    unfold blockDensityBound
    congr 1
    ring
  simpa only [hbound] using exists_circle_hybrid_density
    (ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm
      ha ha' hb hb' e tag) ε hs htotal.le

end Invariant233.OrderedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCircleConditioning
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory

namespace Invariant233.OrderedProductCoupling

theorem left_condExp_eq_circle (P : Parameters) (f : Sample → ℝ) :
    (law P)[f | (inferInstance : MeasurableSpace Endpoint).comap leftEndpoint]
      =ᵐ[law P]
    (law P)[f | (inferInstance : MeasurableSpace ProductModel.Base).comap circleLeftEndpoint] := by
  apply ObservationConditioning.condExp_comap_of_ae_section (law P)
    leftEndpoint_measurable circleLeftEndpoint_measurable
    realEndpoint_measurable circleEndpoint_measurable circleEndpoint_realEndpoint
  exact (ae_real_circle_endpoints P).mono (fun _ h => h.1)

theorem right_condExp_eq_circle (P : Parameters) (f : Sample → ℝ) :
    (law P)[f | (inferInstance : MeasurableSpace Endpoint).comap rightEndpoint]
      =ᵐ[law P]
    (law P)[f | (inferInstance : MeasurableSpace ProductModel.Base).comap circleRightEndpoint] := by
  apply ObservationConditioning.condExp_comap_of_ae_section (law P)
    rightEndpoint_measurable circleRightEndpoint_measurable
    realEndpoint_measurable circleEndpoint_measurable circleEndpoint_realEndpoint
  exact (ae_real_circle_endpoints P).mono (fun _ h => h.2)

theorem left_iCondIndepSet_iff_circle {ι : Type*} [Countable ι]
    (P : Parameters) (events : ι → Set Sample)
    (hmeas : ∀ i, MeasurableSet (events i)) :
    iCondIndepSet ((inferInstance : MeasurableSpace Endpoint).comap leftEndpoint)
      leftEndpoint_measurable.comap_le events (law P) ↔
    iCondIndepSet ((inferInstance : MeasurableSpace ProductModel.Base).comap circleLeftEndpoint)
      circleLeftEndpoint_measurable.comap_le events (law P) := by
  apply ObservationConditioning.iCondIndepSet_comap_iff_of_ae_section (law P)
    leftEndpoint_measurable circleLeftEndpoint_measurable
    realEndpoint_measurable circleEndpoint_measurable circleEndpoint_realEndpoint
    _ events hmeas
  exact (ae_real_circle_endpoints P).mono (fun _ h => h.1)

theorem right_iCondIndepSet_iff_circle {ι : Type*} [Countable ι]
    (P : Parameters) (events : ι → Set Sample)
    (hmeas : ∀ i, MeasurableSet (events i)) :
    iCondIndepSet ((inferInstance : MeasurableSpace Endpoint).comap rightEndpoint)
      rightEndpoint_measurable.comap_le events (law P) ↔
    iCondIndepSet ((inferInstance : MeasurableSpace ProductModel.Base).comap circleRightEndpoint)
      circleRightEndpoint_measurable.comap_le events (law P) := by
  apply ObservationConditioning.iCondIndepSet_comap_iff_of_ae_section (law P)
    rightEndpoint_measurable circleRightEndpoint_measurable
    realEndpoint_measurable circleEndpoint_measurable circleEndpoint_realEndpoint
    _ events hmeas
  exact (ae_real_circle_endpoints P).mono (fun _ h => h.2)

theorem right_threshold_event_ae_eq_circle (P : Parameters) (u : ℕ → ℝ) (i : ℕ) :
    {ω : Sample | u i ≤ rightEndpoint ω i} =ᵐ[law P]
      {ω : Sample | u i ≤ realEndpoint (circleRightEndpoint ω) i} := by
  filter_upwards [ae_real_circle_endpoints P] with ω hω
  change (u i ≤ rightEndpoint ω i) = (u i ≤ realEndpoint (circleRightEndpoint ω) i)
  rw [hω.2]

theorem left_threshold_event_ae_eq_circle (P : Parameters) (u : ℕ → ℝ) (i : ℕ) :
    {ω : Sample | leftEndpoint ω i < u i} =ᵐ[law P]
      {ω : Sample | realEndpoint (circleLeftEndpoint ω) i < u i} := by
  filter_upwards [ae_real_circle_endpoints P] with ω hω
  change (leftEndpoint ω i < u i) = (realEndpoint (circleLeftEndpoint ω) i < u i)
  rw [hω.1]

theorem right_threshold_condExp_eq_circle (P : Parameters) (u : ℕ → ℝ) (i : ℕ) :
    (law P)[({ω : Sample | u i ≤ rightEndpoint ω i}).indicator (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace Endpoint).comap leftEndpoint] =ᵐ[law P]
    (law P)[({ω : Sample | u i ≤ realEndpoint (circleRightEndpoint ω) i}).indicator
      (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace ProductModel.Base).comap circleLeftEndpoint] := by
  exact (left_condExp_eq_circle P _).trans
    (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set
      (right_threshold_event_ae_eq_circle P u i)))

theorem left_threshold_condExp_eq_circle (P : Parameters) (u : ℕ → ℝ) (i : ℕ) :
    (law P)[({ω : Sample | leftEndpoint ω i < u i}).indicator (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace Endpoint).comap rightEndpoint] =ᵐ[law P]
    (law P)[({ω : Sample | realEndpoint (circleLeftEndpoint ω) i < u i}).indicator
      (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace ProductModel.Base).comap circleRightEndpoint] := by
  exact (right_condExp_eq_circle P _).trans
    (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set
      (left_threshold_event_ae_eq_circle P u i)))

theorem right_threshold_iCondIndepSet_iff_circle (P : Parameters) (u : ℕ → ℝ) :
    iCondIndepSet ((inferInstance : MeasurableSpace Endpoint).comap leftEndpoint)
      leftEndpoint_measurable.comap_le
      (fun i => {ω : Sample | u i ≤ rightEndpoint ω i}) (law P) ↔
    iCondIndepSet ((inferInstance : MeasurableSpace ProductModel.Base).comap circleLeftEndpoint)
      circleLeftEndpoint_measurable.comap_le
      (fun i => {ω : Sample | u i ≤ realEndpoint (circleRightEndpoint ω) i}) (law P) := by
  have hraw (i : ℕ) : MeasurableSet {ω : Sample | u i ≤ rightEndpoint ω i} :=
    measurableSet_le measurable_const ((measurable_pi_apply i).comp rightEndpoint_measurable)
  have hcircle (i : ℕ) :
      MeasurableSet {ω : Sample | u i ≤ realEndpoint (circleRightEndpoint ω) i} :=
    measurableSet_le measurable_const
      ((measurable_pi_apply i).comp (realEndpoint_measurable.comp circleRightEndpoint_measurable))
  exact (left_iCondIndepSet_iff_circle P _ hraw).trans
    (ObservationConditioning.iCondIndepSet_iff_of_events_ae_eq
      _ circleLeftEndpoint_measurable.comap_le (law P) _ _ hraw hcircle
      (right_threshold_event_ae_eq_circle P u))

theorem left_threshold_iCondIndepSet_iff_circle (P : Parameters) (u : ℕ → ℝ) :
    iCondIndepSet ((inferInstance : MeasurableSpace Endpoint).comap rightEndpoint)
      rightEndpoint_measurable.comap_le
      (fun i => {ω : Sample | leftEndpoint ω i < u i}) (law P) ↔
    iCondIndepSet ((inferInstance : MeasurableSpace ProductModel.Base).comap circleRightEndpoint)
      circleRightEndpoint_measurable.comap_le
      (fun i => {ω : Sample | realEndpoint (circleLeftEndpoint ω) i < u i}) (law P) := by
  have hraw (i : ℕ) : MeasurableSet {ω : Sample | leftEndpoint ω i < u i} :=
    measurableSet_lt ((measurable_pi_apply i).comp leftEndpoint_measurable) measurable_const
  have hcircle (i : ℕ) :
      MeasurableSet {ω : Sample | realEndpoint (circleLeftEndpoint ω) i < u i} :=
    measurableSet_lt
      ((measurable_pi_apply i).comp (realEndpoint_measurable.comp circleLeftEndpoint_measurable))
      measurable_const
  exact (right_iCondIndepSet_iff_circle P _ hraw).trans
    (ObservationConditioning.iCondIndepSet_iff_of_events_ae_eq
      _ circleRightEndpoint_measurable.comap_le (law P) _ _ hraw hcircle
      (left_threshold_event_ae_eq_circle P u))

end Invariant233.OrderedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductStrictPhaseBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.FloorCocycle

theorem tagged_crossing_of_source_window {m K α x y : ℝ} (k : ℤ)
    (hm : 4 ≤ m) (hK : 0 < K)
    (hαlo : 1 / (m * K) ≤ α) (hαhi : α ≤ 2 / (m * K))
    (hklo : K < |(k : ℝ)|) (hkhi : |(k : ℝ)| ≤ m * K / 4)
    (hx : x < 1 / m) (hy : 1 - 1 / m ≤ y) :
    x < 1 - Int.fract ((k : ℝ) * α) ∧
      1 - Int.fract ((k : ℝ) * α) ≤ y := by
  have hm0 : 0 < m := by linarith
  have hmK : 0 < m * K := mul_pos hm0 hK
  have hα0 : 0 < α := (one_div_pos.mpr hmK).trans_le hαlo
  have hk0 : 0 < |(k : ℝ)| := hK.trans hklo
  have hlo : 1 / m < |(k : ℝ)| * α := by
    calc
      1 / m = K * (1 / (m * K)) := by field_simp
      _ < |(k : ℝ)| * (1 / (m * K)) :=
        mul_lt_mul_of_pos_right hklo (one_div_pos.mpr hmK)
      _ ≤ |(k : ℝ)| * α := mul_le_mul_of_nonneg_left hαlo hk0.le
  have hhalf : |(k : ℝ)| * α ≤ 1 / 2 := by
    calc
      |(k : ℝ)| * α ≤ |(k : ℝ)| * (2 / (m * K)) :=
        mul_le_mul_of_nonneg_left hαhi hk0.le
      _ ≤ (m * K / 4) * (2 / (m * K)) :=
        mul_le_mul_of_nonneg_right hkhi (div_nonneg (by norm_num) hmK.le)
      _ = 1 / 2 := by field_simp <;> ring
  have hinv : 1 / m ≤ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hm
  have hthreshold := threshold_mem_Ioo_of_abs_phase
    (one_div_pos.mpr hm0).le
    (show 1 / m < |(k : ℝ) * α| by
      simpa only [abs_mul, abs_of_pos hα0] using hlo)
    (show |(k : ℝ) * α| < 1 - 1 / m by
      rw [abs_mul, abs_of_pos hα0]
      linarith)
  exact ⟨hx.trans hthreshold.1, hthreshold.2.le.trans hy⟩

end Invariant233.FloorCocycle

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductSourceTagAttenuation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Function Set

namespace Invariant233.ProductCocycle

theorem ae_all_source_tagged_ratios_of_map_ac
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (θ c : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : Summable θ) (hc : ∀ i, 0 ≤ c i)
    (x y : Ω → Space ι) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hacx : μ.map x ≪ haar ι) (hacy : μ.map y ≪ haar ι)
    (horder : ∀ᵐ ω ∂μ, ∀ i, representative (x ω i) ≤ representative (y ω i))
    (m K L : ℝ) (hm : 4 ≤ m) (hK : 0 < K)
    (I : Finset ι) (hlo : ∀ i ∈ I, 1 / (m * K) ≤ θ i)
    (hhi : ∀ i ∈ I, θ i ≤ 2 / (m * K)) (hcost : ∀ i ∈ I, L ≤ c i)
    (E : Set Ω) (htag : ∀ᵐ ω ∂μ, ω ∈ E → ∃ i ∈ I,
      representative (x ω i) < 1 / m ∧ 1 - 1 / m ≤ representative (y ω i)) :
    ∀ᵐ ω ∂μ, ω ∈ E → ∀ k : ℤ,
      K < |(k : ℝ)| → |(k : ℝ)| ≤ m * K / 4 →
      cocycleVersion θ c k (y ω) / cocycleVersion θ c k (x ω) ≤ Real.exp (-L) := by
  filter_upwards [ae_all_int_ratio_bounds_of_map_ac μ θ c hθ0 hθ hc x y
    hx hy hacx hacy horder, htag] with ω hr ht
  intro hE
  obtain ⟨i, hi, hxi, hyi⟩ := ht hE
  intro k hklo hkhi
  have hcross := FloorCocycle.tagged_crossing_of_source_window k hm hK
    (hlo i hi) (hhi i hi) hklo hkhi hxi hyi
  exact ((hr k).2 i hcross).trans (Real.exp_le_exp.mpr (neg_le_neg (hcost i hi)))

end Invariant233.ProductCocycle

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_BlockPhaseConstruction
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace Invariant233.ProductPhases

theorem mem_consecutiveBlock_iff (m : ℕ → ℕ) (j i : ℕ) :
    i ∈ consecutiveBlock m j ↔
      (∑ r ∈ Finset.range j, m r) ≤ i ∧
        i < (∑ r ∈ Finset.range j, m r) + m j := by
  simp [consecutiveBlock]

theorem enumeration_block_of_mem (m : ℕ → ℕ)
    (e : ℕ ≃ Σ j, Fin (m j))
    (he : ∀ a : Σ j, Fin (m j),
      e.symm a = (∑ r ∈ Finset.range a.1, m r) + a.2.val)
    {j i : ℕ} (hi : i ∈ consecutiveBlock m j) : (e i).1 = j := by
  obtain ⟨hlo, hhi⟩ := (mem_consecutiveBlock_iff m j i).mp hi
  let a : Fin (m j) := ⟨i - (∑ r ∈ Finset.range j, m r), by omega⟩
  have ha : e.symm ⟨j, a⟩ = i := by
    rw [he]
    dsimp [a]
    omega
  have heq : e i = ⟨j, a⟩ := by
    rw [← ha, e.apply_symm_apply]
  exact congrArg Sigma.fst heq

end Invariant233.ProductPhases

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductScaleTagAttenuation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductScaleData.mem_earlyCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.ProductScaleLaws

theorem ae_all_source_tagged_ratios {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (j : ℕ) (hb : ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ∈ Set.Icc (1 / p.N j) (2 / p.N j))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x y : Ω → ProductCocycle.Space ℕ)
    (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hacx : μ.map x ≪ ProductCocycle.haar ℕ)
    (hacy : μ.map y ≪ ProductCocycle.haar ℕ)
    (horder : ∀ᵐ ω ∂μ, ∀ i,
      ProductCocycle.representative (x ω i) ≤ ProductCocycle.representative (y ω i))
    (E : Set Ω) (htag : ∀ᵐ ω ∂μ, ω ∈ E →
      ∃ i ∈ ProductPhases.consecutiveBlock p.m j,
        ProductCocycle.representative (x ω i) < 1 / (p.m j : ℝ) ∧
        1 - 1 / (p.m j : ℝ) ≤ ProductCocycle.representative (y ω i)) :
    ∀ᵐ ω ∂μ, ω ∈ E → ∀ k : ℤ,
      (p.K j : ℝ) < |(k : ℝ)| → |(k : ℝ)| ≤ p.N j / 4 →
      ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (y ω) /
        ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (x ω) ≤
          Real.exp (-p.L j) := by
  have hC (s : ℕ) : p.L s ≤ p.C s := by
    rw [hp.C_eq s]
    exact le_max_left _ _
  have hcost (i : ℕ) (hi : i ∈ ProductPhases.consecutiveBlock p.m j) :
      p.L j ≤ p.C (e i).1 := by
    rw [ProductPhases.enumeration_block_of_mem p.m e he hi]
    exact hC j
  exact ProductCocycle.ae_all_source_tagged_ratios_of_map_ac μ θ
    (fun i => p.C (e i).1) hθ0 hθ
    (fun i => (by norm_num : (0 : ℝ) ≤ 1).trans
      ((hp.L_ge_one (e i).1).trans (hC (e i).1)))
    x y hx hy hacx hacy horder (p.m j) (p.K j) (p.L j)
    (by exact_mod_cast (show 4 ≤ p.m j by have := hp.m_ge_100 j; omega))
    (by exact_mod_cast hp.K_pos j)
    (ProductPhases.consecutiveBlock p.m j)
    (fun i hi => (hb i hi).1) (fun i hi => (hb i hi).2) hcost E htag

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductTailScaleCover
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set

namespace Invariant233.ProductPhases

open TailScaleCover

theorem exists_tail_thresholds
    {ι : Type*} (J : ℕ → Finset ι) (K G κ L C : ℕ → ℝ) (θ : ι → ℝ)
    (j : ℕ)
    (hsize : ∀ s, j ≤ s → 100 ≤ (J s).card)
    (hgrowth : ∀ s, j ≤ s → 2 ^ s ≤ (J s).card)
    (hG : ∀ s, j ≤ s → 1 ≤ G s ∧ 4 * G s ≤ ((J s).card : ℝ))
    (hgap : ∀ s, j ≤ s → G (s + 1) * K (s + 1) < upperHorizon (J s).card)
    (hL : ∀ s, j ≤ s → L j ≤ L s)
    (hC : ∀ s, j ≤ s → L s ≤ C s)
    (hlargeIntensity : ∀ s, j ≤ s → L s ≤ κ s * ((J s).card : ℝ) ^ (1 / 40 : ℝ))
    (hsmallIntensity : ∀ s, j ≤ s → L s ≤ κ (s + 1) * Real.sqrt (G (s + 1)))
    (hsmall : ∀ s, j < s → smallPhaseCondition (J s) (K s) (G s) θ)
    (hlarge : ∀ s, j ≤ s → largePhaseCondition (J s) (((J s).card : ℝ) * K s) θ)
    (k : ℤ) (hk : ((J j).card : ℝ) * K j / 4 ≤ |(k : ℝ)|) :
    ∃ (s : ℕ) (w : ℝ) (I : Finset ι),
      j ≤ s ∧ (w = ((J s).card : ℝ) ^ (-(19 / 20 : ℝ)) ∨
        (j < s ∧ w = G s / (J s).card)) ∧
      w ∈ Set.Icc (1 / ((J s).card : ℝ)) (1 / 4) ∧
      I ⊆ J s ∧ ((J s).card : ℝ) / 20 ≤ I.card ∧
      (∀ i ∈ I, 1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Icc w (1 - w)) ∧
      L j ≤ ((J s).card : ℝ) * CouplingMarginalBounds.rho (κ s) (J s).card w ∧
      L j ≤ C s := by
  classical
  have hunbounded (R : ℝ) : ∃ s, j ≤ s ∧ R ≤ upperHorizon (J s).card := by
    obtain ⟨n, hn⟩ := exists_nat_gt R
    let s := max j n
    have hjs : j ≤ s := le_max_left _ _
    have hsm : s ≤ (J s).card := (Nat.lt_two_pow_self (n := s)).le.trans (hgrowth s hjs)
    refine ⟨s, hjs, ?_⟩
    calc
      R ≤ (n : ℝ) := hn.le
      _ ≤ (s : ℝ) := by exact_mod_cast le_max_right j n
      _ ≤ ((J s).card : ℝ) := by exact_mod_cast hsm
      _ ≤ upperHorizon (J s).card := self_le_upperHorizon (by
        have := hsize s hjs
        omega)
  obtain ⟨s, hjs, hs⟩ := exists_window (fun s => G s * K s)
    (fun s => ((J s).card : ℝ) * K s / 4) (fun s => upperHorizon (J s).card)
    j (fun s hs => (hgap s hs).le) hunbounded hk
  have hm100 : (100 : ℝ) ≤ (J s).card := by exact_mod_cast hsize s hjs
  have hm : (0 : ℝ) < (J s).card := by linarith
  have hwidths := widths_mem_Icc (by linarith : (16 : ℝ) ≤ (J s).card)
    (hG s hjs).1 (hG s hjs).2
  have hcost : L j ≤ C s := (hL s hjs).trans (hC s hjs)
  rcases hs with hhigh | hlow
  · let w : ℝ := ((J s).card : ℝ) ^ (-(19 / 20 : ℝ))
    have hcount : ((J s).card : ℝ) / 20 ≤
        (((J s).filter (fun i =>
          1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Icc w (1 - w))).card : ℝ) := by
      simpa only [phaseGoodCount, w, neg_div] using
        hlarge s hjs k hhigh.1 hhigh.2
    refine ⟨s, w, (J s).filter (fun i =>
        1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Icc w (1 - w)),
      hjs, Or.inl rfl, hwidths.2, Finset.filter_subset _ _,
      hcount, ?_, ?_, hcost⟩
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · rw [show w = ((J s).card : ℝ) ^ (-(19 / 20 : ℝ)) from rfl,
        intensity_large _ _ hm]
      exact (hL s hjs).trans (hlargeIntensity s hjs)
  · refine ⟨s, G s / (J s).card, J s, hjs, Or.inr ⟨hlow.1, rfl⟩,
      hwidths.1, Finset.Subset.refl _, ?_,
      hsmall s hlow.1 k hlow.2.1 hlow.2.2, ?_, hcost⟩
    · linarith [hm.le]
    · rw [intensity_small _ _ _ hm (by linarith [(hG s hjs).1])]
      have hprev : j ≤ s - 1 := by omega
      have hi := hsmallIntensity (s - 1) hprev
      rw [Nat.sub_add_cancel (by omega : 1 ≤ s)] at hi
      exact (hL (s - 1) hprev).trans hi

end Invariant233.ProductPhases

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductScaleTailAssignment
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductPhases.card_consecutiveBlock _root_.OAI.Invariant233.ProductScaleData.mem_earlyCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233.ProductScaleLaws

variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem exists_phase_tail_thresholds (θ : ℕ → ℝ) (j : ℕ)
    (hsmall : ∀ s, j < s → ProductPhases.smallPhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.K s) (p.G s) θ)
    (hlarge : ∀ s, j ≤ s → ProductPhases.largePhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.N s) θ)
    (k : ℤ) (hk : p.N j / 4 ≤ |(k : ℝ)|) :
    ∃ (s : ℕ) (w : ℝ) (I : Finset ℕ),
      j ≤ s ∧ (w = p.b s ∨ (j < s ∧ w = p.a s)) ∧
      w ∈ Set.Icc (1 / (p.m s : ℝ)) (1 / 4) ∧
      I ⊆ ProductPhases.consecutiveBlock p.m s ∧ (p.m s : ℝ) / 20 ≤ I.card ∧
      (∀ i ∈ I, 1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Icc w (1 - w)) ∧
      p.L j ≤ (p.m s : ℝ) * CouplingMarginalBounds.rho
        (ProductScaleData.kappa s) (p.m s) w ∧ p.L j ≤ p.C s := by
  have hcard (s : ℕ) : (ProductPhases.consecutiveBlock p.m s).card = p.m s := by
    simp [ProductPhases.consecutiveBlock]
  have hgrowth (s : ℕ) : 2 ^ s ≤ p.m s := by
    have h := hp.m_ge_pow s
    rw [pow_succ] at h
    have : 0 < 2 ^ s := by positivity
    omega
  have hG (s : ℕ) : (1 : ℝ) ≤ p.G s ∧ 4 * (p.G s : ℝ) ≤ p.m s := by
    constructor
    · exact_mod_cast hp.G_pos s
    · exact_mod_cast hp.m_ge_G s
  have hC (s : ℕ) : p.L s ≤ p.C s := by
    rw [hp.C_eq s]
    exact le_max_left _ _
  have h := ProductPhases.exists_tail_thresholds
    (ProductPhases.consecutiveBlock p.m) (fun s => (p.K s : ℝ))
    (fun s => (p.G s : ℝ)) ProductScaleData.kappa p.L p.C θ j
    (by simpa only [hcard] using fun s (_ : j ≤ s) => hp.m_ge_100 s)
    (by simpa only [hcard] using fun s (_ : j ≤ s) => hgrowth s)
    (by simpa only [hcard] using fun s (_ : j ≤ s) => hG s)
    (by simpa only [hcard, TailScaleCover.upperHorizon] using
      fun s (_ : j ≤ s) => hp.next_gap s)
    (fun s hs => hp.L_monotone hs)
    (fun s _ => hC s)
    (by simpa only [hcard] using fun s (_ : j ≤ s) => hp.m_attenuation s)
    (fun s _ => hp.gain_attenuation s)
    hsmall
    (by simpa only [hcard, ProductScaleData.N] using hlarge)
    k (by simpa only [hcard, ProductScaleData.N] using hk)
  simpa only [hcard, ProductScaleData.a, ProductScaleData.b] using h

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductScaleTailAttenuation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductScaleData.mem_earlyCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Invariant233.ProductScaleLaws
variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem product_tail_conditional_attenuation
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    {Ω : Type*} (mx my : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (hmx : mx ≤ mΩ) (hmy : my ≤ mΩ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (x y : Ω → ProductCocycle.Space ℕ) (hx : Measurable[mx] x) (hy : Measurable[my] y)
    (hacx : μ.map x ≪ ProductCocycle.haar ℕ) (hacy : μ.map y ≪ ProductCocycle.haar ℕ)
    (horder : ∀ᵐ ω ∂μ, ∀ i,
      ProductCocycle.representative (x ω i) ≤ ProductCocycle.representative (y ω i))
    (top bottom : Bool → ℕ → Set Ω)
    (htop : ∀ which i, MeasurableSet (top which i))
    (hbottom : ∀ which i, MeasurableSet (bottom which i))
    (hindTop : ∀ which, iCondIndepSet mx hmx (top which) μ)
    (hindBottom : ∀ which, iCondIndepSet my hmy (bottom which) μ)
    (j : ℕ)
    (hb : ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ∈ Icc (1 / p.N j) (2 / p.N j))
    (hsmall : ∀ s, j < s → ProductPhases.smallPhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.K s) (p.G s) θ)
    (hlarge : ∀ s, j ≤ s → ProductPhases.largePhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.N s) θ)
    (k : ℤ) (hk : (p.K j : ℝ) < |(k : ℝ)|)
    (hlabels : ∀ s, j ≤ s → ∀ which : Bool, ∀ i ∈ ProductPhases.consecutiveBlock p.m s,
      let u := 1 - Int.fract ((k : ℝ) * θ i)
      u ∈ Icc (if which then p.b s else p.a s)
        (1 - (if which then p.b s else p.a s)) → ∀ᵐ ω ∂μ,
        (ProductCocycle.representative (x ω i) < u → ω ∈ top which i → u ≤ ProductCocycle.representative (y ω i)) ∧
        (u ≤ ProductCocycle.representative (y ω i) → ω ∈ bottom which i → ProductCocycle.representative (x ω i) < u) ∧
        (ProductCocycle.representative (x ω i) < u →
          (ProductScaleData.kappa s * Real.sqrt ((if which then p.b s else p.a s) / (p.m s : ℝ))) / 10 ≤
            (μ[(top which i).indicator (fun _ => (1 : ℝ)) | mx]) ω) ∧
        (u ≤ ProductCocycle.representative (y ω i) →
          (ProductScaleData.kappa s * Real.sqrt ((if which then p.b s else p.a s) / (p.m s : ℝ))) / 10 ≤
            (μ[(bottom which i).indicator (fun _ => (1 : ℝ)) | my]) ω))
    (E : Set Ω) (htag : ∀ᵐ ω ∂μ, ω ∈ E → ∃ i ∈ ProductPhases.consecutiveBlock p.m j,
      ProductCocycle.representative (x ω i) < 1 / (p.m j : ℝ) ∧
        1 - 1 / (p.m j : ℝ) ≤ ProductCocycle.representative (y ω i))
    : ∃ H₁ H₂ : Set Ω, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂μ, (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂μ, (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂μ, ω ∈ E →
        ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (y ω) / ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (x ω) ≤
          Real.exp (-p.L j) + H₁.indicator (fun _ => (1 : ℝ)) ω +
            H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  have hc : ∀ i, 0 ≤ p.C (e i).1 := by
    intro i
    rw [hp.C_eq]
    exact (by norm_num : (0 : ℝ) ≤ 1).trans
      ((hp.L_ge_one _).trans (le_max_left _ _))
  by_cases hnear : |(k : ℝ)| ≤ p.N j / 4
  · apply CrossingAvoidance.empty_exceptional_events mx my μ E
      (fun ω => ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (y ω) /
        ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (x ω))
      (Real.exp (-p.L j)) (Real.exp (-p.L j / 400)) (Real.exp_pos _).le
    exact (hp.ae_all_source_tagged_ratios e he θ hθ0 hθsum j hb μ x y
      (hx.mono hmx le_rfl).aemeasurable (hy.mono hmy le_rfl).aemeasurable
      hacx hacy horder E htag).mono (fun _ h hE => h hE k hk hnear)
  · obtain ⟨s, w, I, hjs, hw, _hwidth, hIs, hI, hthreshold, hIntensity, hcost⟩ :=
      hp.exists_phase_tail_thresholds θ j hsmall hlarge k (le_of_not_ge hnear)
    obtain ⟨which, rfl⟩ : ∃ which : Bool, w = if which then p.b s else p.a s := by
      rcases hw with hw | ⟨_, hw⟩
      · exact ⟨true, by simpa using hw⟩
      · exact ⟨false, by simpa using hw⟩
    let w : ℝ := if which then p.b s else p.a s
    let ρ : ℝ := ProductScaleData.kappa s * Real.sqrt (w / (p.m s : ℝ))
    have hρ : 0 ≤ ρ := mul_nonneg
      (by unfold ProductScaleData.kappa; positivity) (Real.sqrt_nonneg _)
    have hl : ∀ᵐ ω ∂μ, ∀ i ∈ I,
        (ProductCocycle.representative (x ω i) < 1 - Int.fract ((k : ℝ) * θ i) →
          ω ∈ top which i → 1 - Int.fract ((k : ℝ) * θ i) ≤ ProductCocycle.representative (y ω i)) ∧
        (1 - Int.fract ((k : ℝ) * θ i) ≤ ProductCocycle.representative (y ω i) →
          ω ∈ bottom which i → ProductCocycle.representative (x ω i) < 1 - Int.fract ((k : ℝ) * θ i)) ∧
        (ProductCocycle.representative (x ω i) < 1 - Int.fract ((k : ℝ) * θ i) →
          ρ / 10 ≤ (μ[(top which i).indicator (fun _ => (1 : ℝ)) | mx]) ω) ∧
        (1 - Int.fract ((k : ℝ) * θ i) ≤ ProductCocycle.representative (y ω i) →
          ρ / 10 ≤ (μ[(bottom which i).indicator (fun _ => (1 : ℝ)) | my]) ω) := by
      apply ae_all_iff.mpr
      intro i
      apply ae_all_iff.mpr
      intro hi
      exact hlabels s hjs which i (hIs hi) (hthreshold i hi)
    have hcostI : ∀ i ∈ I, p.L j ≤ p.C (e i).1 := by
      intro i hi
      rw [ProductPhases.enumeration_block_of_mem p.m e he (hIs hi)]
      exact hcost
    obtain ⟨H₁, H₂, hm₁, hm₂, hb₁, hb₂, hr⟩ :=
      ProductCocycle.finite_conditional_attenuation_of_map_ac mx my hmx hmy μ
        θ (fun i => p.C (e i).1) hθ0 hθsum hc k I x y hx hy hacx hacy
        (top which) (bottom which) (htop which) (hbottom which)
        (hindTop which) (hindBottom which) (p.m s) ρ (p.L j) hρ hIntensity hI hcostI
        horder
        (hl.mono (fun _ h i hi => (h i hi).1))
        (hl.mono (fun _ h i hi => (h i hi).2.1))
        (hl.mono (fun _ h i hi => (h i hi).2.2.1))
        (hl.mono (fun _ h i hi => (h i hi).2.2.2))
    exact ⟨H₁, H₂, hm₁, hm₂, hb₁, hb₂, hr.mono (fun _ h _ => h)⟩

theorem simultaneous_product_tail_conditional_attenuation
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    {Ω : Type*} (mx my : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (hmx : mx ≤ mΩ) (hmy : my ≤ mΩ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (x y : Ω → ProductCocycle.Space ℕ) (hx : Measurable[mx] x) (hy : Measurable[my] y)
    (hacx : μ.map x ≪ ProductCocycle.haar ℕ) (hacy : μ.map y ≪ ProductCocycle.haar ℕ)
    (horder : ∀ᵐ ω ∂μ, ∀ i,
      ProductCocycle.representative (x ω i) ≤ ProductCocycle.representative (y ω i))
    (top bottom : ℤ → Bool → ℕ → Set Ω)
    (htop : ∀ k which i, MeasurableSet (top k which i))
    (hbottom : ∀ k which i, MeasurableSet (bottom k which i))
    (hindTop : ∀ k which, iCondIndepSet mx hmx (top k which) μ)
    (hindBottom : ∀ k which, iCondIndepSet my hmy (bottom k which) μ)
    (j : ℕ)
    (hb : ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ∈ Icc (1 / p.N j) (2 / p.N j))
    (hsmall : ∀ s, j < s → ProductPhases.smallPhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.K s) (p.G s) θ)
    (hlarge : ∀ s, j ≤ s → ProductPhases.largePhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.N s) θ)
    (hlabels : ∀ k : ℤ, ∀ s, j ≤ s → ∀ which : Bool, ∀ i ∈ ProductPhases.consecutiveBlock p.m s,
      let u := 1 - Int.fract ((k : ℝ) * θ i)
      u ∈ Icc (if which then p.b s else p.a s)
        (1 - (if which then p.b s else p.a s)) → ∀ᵐ ω ∂μ,
        (ProductCocycle.representative (x ω i) < u → ω ∈ top k which i → u ≤ ProductCocycle.representative (y ω i)) ∧
        (u ≤ ProductCocycle.representative (y ω i) → ω ∈ bottom k which i → ProductCocycle.representative (x ω i) < u) ∧
        (ProductCocycle.representative (x ω i) < u →
          (ProductScaleData.kappa s * Real.sqrt ((if which then p.b s else p.a s) / (p.m s : ℝ))) / 10 ≤
            (μ[(top k which i).indicator (fun _ => (1 : ℝ)) | mx]) ω) ∧
        (u ≤ ProductCocycle.representative (y ω i) →
          (ProductScaleData.kappa s * Real.sqrt ((if which then p.b s else p.a s) / (p.m s : ℝ))) / 10 ≤
            (μ[(bottom k which i).indicator (fun _ => (1 : ℝ)) | my]) ω))
    (E : Set Ω) (htag : ∀ᵐ ω ∂μ, ω ∈ E → ∃ i ∈ ProductPhases.consecutiveBlock p.m j,
      ProductCocycle.representative (x ω i) < 1 / (p.m j : ℝ) ∧
        1 - 1 / (p.m j : ℝ) ≤ ProductCocycle.representative (y ω i))
    : ∃ H₁ H₂ : ℤ → Set Ω,
      (∀ k, MeasurableSet (H₁ k)) ∧ (∀ k, MeasurableSet (H₂ k)) ∧
      (∀ᵐ ω ∂μ, ∀ k : ℤ, (p.K j : ℝ) < |(k : ℝ)| →
        (μ[(H₁ k).indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ Real.exp (-p.L j / 400) ∧
        (μ[(H₂ k).indicator (fun _ => (1 : ℝ)) | my]) ω ≤ Real.exp (-p.L j / 400) ∧
        (ω ∈ E →
          ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (y ω) /
            ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (x ω) ≤
            Real.exp (-p.L j) + (H₁ k).indicator (fun _ => (1 : ℝ)) ω +
              (H₂ k).indicator (fun _ => (1 : ℝ)) ω)) := by
  classical
  let R : ℤ → Ω → ℝ := fun k ω => if (p.K j : ℝ) < |(k : ℝ)| then
    ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (y ω) /
      ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (x ω) else 0
  have hEach (k : ℤ) : ∃ H₁ H₂ : Set Ω, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂μ, (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂μ, (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂μ, ω ∈ E → R k ω ≤ Real.exp (-p.L j) +
        H₁.indicator (fun _ => (1 : ℝ)) ω + H₂.indicator (fun _ => (1 : ℝ)) ω) := by
    by_cases hk : (p.K j : ℝ) < |(k : ℝ)|
    · simpa only [R, ite_eq_left hk] using hp.product_tail_conditional_attenuation
        e he θ hθ0 hθsum mx my hmx hmy μ x y hx hy hacx hacy horder
        (top k) (bottom k) (htop k) (hbottom k) (hindTop k) (hindBottom k)
        j hb hsmall hlarge k hk (hlabels k) E htag
    · apply CrossingAvoidance.empty_exceptional_events mx my μ E (R k)
        (Real.exp (-p.L j)) (Real.exp (-p.L j / 400)) (Real.exp_pos _).le
      exact Filter.Eventually.of_forall (fun _ _ => by
        simpa only [R, ite_eq_right hk] using (Real.exp_pos (-p.L j)).le)
  obtain ⟨H₁, H₂, hm₁, hm₂, h⟩ := CrossingAvoidance.simultaneous_exceptional_families
    mx my μ E R (fun _ => Real.exp (-p.L j)) (fun _ => Real.exp (-p.L j / 400)) hEach
  refine ⟨H₁, H₂, hm₁, hm₂, h.mono ?_⟩
  intro ω hω k hk
  simpa only [R, ite_eq_left hk] using hω k

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_SourceProductTailAttenuation
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Invariant233.ProductScaleLaws
open OrderedProductCoupling

variable {p : ProductScaleData} (hp : ProductScaleLaws p)

theorem source_product_tail_conditional_attenuation
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (j : ℕ)
    (hb : ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ∈ Icc (1 / p.N j) (2 / p.N j))
    (hsmall : ∀ s, j < s → ProductPhases.smallPhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.K s) (p.G s) θ)
    (hlarge : ∀ s, j ≤ s → ProductPhases.largePhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.N s) θ) :
    let P := sourceBlocks p.m p.a p.b hp.m_ge_100
      (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
      (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j
    ∃ H₁ H₂ : ℤ → Set Sample,
      (∀ k, MeasurableSet (H₁ k)) ∧ (∀ k, MeasurableSet (H₂ k)) ∧
      (∀ᵐ ω ∂law P, ∀ k : ℤ, (p.K j : ℝ) < |(k : ℝ)| →
        ((law P)[(H₁ k).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap circleLeftEndpoint inferInstance]) ω ≤
            Real.exp (-p.L j / 400) ∧
        ((law P)[(H₂ k).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap circleRightEndpoint inferInstance]) ω ≤
            Real.exp (-p.L j / 400) ∧
        ((∃ i ∈ ProductPhases.consecutiveBlock p.m j,
          circleRepresentative (circleLeftEndpoint ω i) < 1 / (p.m j : ℝ) ∧
          1 - 1 / (p.m j : ℝ) ≤ circleRepresentative (circleRightEndpoint ω i)) →
          ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (circleRightEndpoint ω) /
            ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (circleLeftEndpoint ω) ≤
            Real.exp (-p.L j) + (H₁ k).indicator (fun _ => (1 : ℝ)) ω +
              (H₂ k).indicator (fun _ => (1 : ℝ)) ω)) := by
  let P := sourceBlocks p.m p.a p.b hp.m_ge_100
    (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
    (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j
  change ∃ H₁ H₂ : ℤ → Set Sample, _
  let u : ℤ → ℕ → ℝ := fun k i => 1 - Int.fract ((k : ℝ) * θ i)
  let top : ℤ → Bool → ℕ → Set Sample := fun k _ i =>
    {ω | u k i ≤ realEndpoint (circleRightEndpoint ω) i}
  let bottom : ℤ → Bool → ℕ → Set Sample := fun k _ i =>
    {ω | realEndpoint (circleLeftEndpoint ω) i < u k i}
  have htop (k : ℤ) (which : Bool) (i : ℕ) : MeasurableSet (top k which i) :=
    measurableSet_le measurable_const
      ((measurable_pi_apply i).comp (realEndpoint_measurable.comp circleRightEndpoint_measurable))
  have hbottom (k : ℤ) (which : Bool) (i : ℕ) : MeasurableSet (bottom k which i) :=
    measurableSet_lt
      ((measurable_pi_apply i).comp (realEndpoint_measurable.comp circleLeftEndpoint_measurable))
      measurable_const
  have hac (side : Bool) : (law P).map (circleHybridEndpoint (fun _ => side)) ≪
      ProductCocycle.haar ℕ := by
    obtain ⟨g, _, _, _, _, hg⟩ := exists_source_circle_hybrid_density p.m p.a p.b
      hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
      (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j (fun _ => side)
    change (law P).map (circleHybridEndpoint (fun _ => side)) = _ at hg
    rw [hg]
    exact withDensity_absolutelyContinuous _ _
  have hacx : (law P).map circleLeftEndpoint ≪ ProductCocycle.haar ℕ := hac false
  have hacy : (law P).map circleRightEndpoint ≪ ProductCocycle.haar ℕ := hac true
  apply hp.simultaneous_product_tail_conditional_attenuation e he θ hθ0 hθsum
    (MeasurableSpace.comap circleLeftEndpoint inferInstance)
    (MeasurableSpace.comap circleRightEndpoint inferInstance)
    circleLeftEndpoint_measurable.comap_le circleRightEndpoint_measurable.comap_le
    (law P) circleLeftEndpoint circleRightEndpoint
    (Measurable.of_comap_le le_rfl) (Measurable.of_comap_le le_rfl)
    hacx hacy (ae_circle_endpoints_ordered P) top bottom htop hbottom
    (fun k _ => (right_threshold_iCondIndepSet_iff_circle P (u k)).mp
      (right_thresholds_iCondIndepSet P (u k)))
    (fun k _ => (left_threshold_iCondIndepSet_iff_circle P (u k)).mp
      (left_thresholds_iCondIndepSet P (u k)))
    j hb hsmall hlarge
  · intro k s _hjs which i hi _u hu
    have hsi := ProductPhases.enumeration_block_of_mem p.m e he hi
    let w : ℝ := if which then p.b s else p.a s
    have hw : w = P.a i ∨ w = P.b i := by
      cases which
      · exact Or.inl (by simp only [w, P, sourceBlocks, ofBlocks, hsi, Bool.false_eq_true, ↓reduceIte])
      · exact Or.inr (by simp only [w, P, sourceBlocks, ofBlocks, hsi, ↓reduceIte])
    have hrho : CouplingMarginalBounds.rho (P.κ i) (P.m i) w =
        ProductScaleData.kappa s * Real.sqrt (w / (p.m s : ℝ)) := by
      simp only [CouplingMarginalBounds.rho, P, sourceBlocks, ofBlocks, hsi,
        sourceKappa, ProductScaleData.kappa, Nat.cast_add, Nat.cast_one]
    filter_upwards [ae_real_circle_endpoints P,
      right_threshold_condExp_lower P (u k), left_threshold_condExp_lower P (u k),
      right_threshold_condExp_eq_circle P (u k) i,
      left_threshold_condExp_eq_circle P (u k) i]
      with ω hrep hr hl her hel
    refine ⟨fun _ h => h, fun _ h => h, ?_, ?_⟩
    · intro hx
      have hxr : leftEndpoint ω i < u k i := by
        rw [← hrep.1]
        exact hx
      have h := hr i w hw hu.1 hu.2 hxr
      rw [hrho, her] at h
      exact h
    · intro hy
      have hyr : u k i ≤ rightEndpoint ω i := by
        rw [← hrep.2]
        exact hy
      have h := hl i w hw hu.1 hu.2 hyr
      rw [hrho, hel] at h
      exact h
  · exact Filter.Eventually.of_forall (fun _ h => h)

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_SourceProductTailRealization
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace Invariant233.ProductScaleLaws
open OrderedProductCoupling
variable {p : ProductScaleData} (hp : ProductScaleLaws p)

theorem eventually_source_product_tail_estimate_oai
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (hb : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ∈ Icc (1 / p.N j) (2 / p.N j))
    (hsmall : ∀ s, ProductPhases.smallPhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.K s) (p.G s) θ)
    (hlarge : ∀ᶠ s in atTop, ProductPhases.largePhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.N s) θ) :
    ∀ᶠ j in atTop, SourceTailEstimate p e θ j
      (sourceBlocks p.m p.a p.b hp.m_ge_100
        (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
        (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j) := by
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hlarge
  filter_upwards [eventually_ge_atTop j₀] with j hj
  exact hp.source_product_tail_conditional_attenuation e he θ hθ0 hθsum j
    (hb j) (fun s _ => hsmall s) (fun s hjs => hj₀ s (hj.trans hjs))

end Invariant233.ProductScaleLaws

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.ProductScaleLaws.eventually_source_product_tail_estimate_oai := @OAI.Invariant233.ProductScaleLaws.eventually_source_product_tail_estimate_oai
