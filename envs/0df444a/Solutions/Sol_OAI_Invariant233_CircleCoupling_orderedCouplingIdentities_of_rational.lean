-- Prove2me | solution 1 for OAI.Invariant233.CircleCoupling.orderedCouplingIdentities_of_rational
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:32:13.547217+00:00
-- url     : https://prove2.me/submissions/01c55f18-2dfd-451e-a043-2135beda7d17

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003
import Theorems.Thm_OAI_Invariant233_CircleCoupling_ae_endpointPairLaw_ratio_cap
import Theorems.Thm_OAI_Invariant233_CircleCoupling_ae_endpoint_ratio_cap
import Theorems.Thm_OAI_Invariant233_CircleCoupling_ae_hybridPairLaw_ratio_cap

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_CappedRatios
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233

variable {X : Type*}

theorem continuousOn_capped_ratio [TopologicalSpace X]
    (F : X → ℝ) (Q : Set X) (hF : ContinuousOn F Q)
    (hFp : ∀ x ∈ Q, F x ≠ 0) (B : ℝ) :
    ContinuousOn (fun t : X × X => (Complex.ofReal (min B (F t.2 / F t.1)))) (Q ×ˢ Q) := by
  have hfst : ContinuousOn (fun t : X × X => F t.1) (Q ×ˢ Q) :=
    hF.comp continuous_fst.continuousOn (fun _ ht => ht.1)
  have hsnd : ContinuousOn (fun t : X × X => F t.2) (Q ×ˢ Q) :=
    hF.comp continuous_snd.continuousOn (fun _ ht => ht.2)
  have hratio : ContinuousOn (fun t : X × X => F t.2 / F t.1) (Q ×ˢ Q) :=
    hsnd.div hfst (fun t ht => hFp t.1 ht.1)
  exact Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.inf hratio)

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_CompactTransfer
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Invariant233.CompactTransfer

theorem measure_compl_le_of_tendsto {X ι : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {L : Filter ι} [L.NeBot]
    {ν : FiniteMeasure X} {νs : ι → FiniteMeasure X}
    (hν : Tendsto νs L (𝓝 ν)) {K : Set X} (hK : IsClosed K)
    {ε : ℝ≥0∞} (hbound : ∀ᶠ i in L, (νs i : Measure X) Kᶜ ≤ ε) :
    (ν : Measure X) Kᶜ ≤ ε := by
  have hmass : Tendsto (fun i => (νs i : Measure X) Set.univ) L
      (𝓝 ((ν : Measure X) Set.univ)) := by
    simpa only [← FiniteMeasure.ennreal_mass, Function.comp_def] using
      ENNReal.continuous_coe.continuousAt.tendsto.comp hν.mass
  have hparts : ∀ᶠ i in L,
      (νs i : Measure X) Set.univ ≤ (νs i : Measure X) K + ε := by
    filter_upwards [hbound] with i hi
    rw [← measure_add_measure_compl hK.measurableSet]
    exact add_le_add le_rfl hi
  have hlim := Filter.limsup_le_limsup hparts
  rw [hmass.limsup_eq,
    limsup_add_const L (fun i => (νs i : Measure X) K) ε
      (by isBoundedDefault) (by isBoundedDefault)] at hlim
  have htotal := hlim.trans (add_le_add
    (FiniteMeasure.limsup_measure_closed_le_of_tendsto hν hK) le_rfl)
  rw [measure_compl hK.measurableSet (measure_ne_top _ _), tsub_le_iff_right]
  simpa only [add_comm] using htotal

theorem ae_mem_of_closed_approximation {X ι : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {L : Filter ι} [L.NeBot]
    {ν : FiniteMeasure X} {νs : ι → FiniteMeasure X}
    (hν : Tendsto νs L (𝓝 ν)) {S : Set X}
    (happrox : ∀ ε : ℝ≥0, 0 < ε → ∃ K : Set X,
      IsClosed K ∧ K ⊆ S ∧ ∀ᶠ i in L, (νs i : Measure X) Kᶜ ≤ ε) :
    ∀ᵐ x ∂(ν : Measure X), x ∈ S := by
  apply ae_iff.mpr
  change (ν : Measure X) Sᶜ = 0
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨K, hK, hKS, hbound⟩ := happrox ε hε
  simpa using
    (measure_mono (Set.compl_subset_compl.mpr hKS)).trans
      (measure_compl_le_of_tendsto hν hK hbound)

end Invariant233.CompactTransfer

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_CountableGraphTransfer
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Invariant233.Fields

variable {X Y Ω ι : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [Countable ι] {μ : Measure X} {ν : Measure Ω}

theorem ae_relation_of_countable_graphs
    (P : X → Y → Prop) (t : ι → X → Y) (x : Ω → X) (y : Ω → Y)
    (hx : AEMeasurable x ν) (hμ : ν.map x ≪ μ)
    (hgraph : ∀ i, ∀ᵐ z ∂μ, P z (t i z))
    (hsupport : ∀ᵐ ω ∂ν, ∃ i, y ω = t i (x ω)) :
    ∀ᵐ ω ∂ν, P (x ω) (y ω) := by
  have hcommon : ∀ᵐ z ∂μ, ∀ i, P z (t i z) := ae_all_iff.mpr hgraph
  have hpull : ∀ᵐ ω ∂ν, ∀ i, P (x ω) (t i (x ω)) :=
    ae_of_ae_map hx (hμ.ae_le hcommon)
  filter_upwards [hpull, hsupport] with ω hω hωsupport
  obtain ⟨i, hi⟩ := hωsupport
  rw [hi]
  exact hω i

theorem ae_pair_relation_of_countable_graphs [MeasurableSpace Y]
    {β : Measure (X × Y)} (P : X → Y → Prop) (t : ι → X → Y)
    (hμ : β.map Prod.fst ≪ μ)
    (hgraph : ∀ i, ∀ᵐ z ∂μ, P z (t i z))
    (hsupport : ∀ᵐ z ∂β, ∃ i, z.2 = t i z.1) :
    ∀ᵐ z ∂β, P z.1 z.2 :=
  ae_relation_of_countable_graphs P t Prod.fst Prod.snd
    measurable_fst.aemeasurable hμ hgraph hsupport

end Invariant233.Fields

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_EndpointLoss
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory Set
open scoped Topology RealInnerProductSpace

namespace Invariant233.EndpointLoss

variable {X : Type*} [MeasurableSpace X]

theorem sqrt_integral_sq_eq_norm {μ : Measure X} (f : Lp ℝ 2 μ) :
    Real.sqrt (∫ x, f x ^ 2 ∂μ) = ‖f‖ := by
  have hs : (∫ x, f x ^ 2 ∂μ) = ‖f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [hs, Real.sqrt_sq (norm_nonneg f)]

theorem setIntegral_density_le_sqrt
    (μ : Measure X) [IsFiniteMeasure μ] {h : X → ℝ}
    (hh : MemLp h 2 μ) (h_nonneg : 0 ≤ᵐ[μ] h)
    {s : Set X} (hs : MeasurableSet s) :
    (∫ x in s, h x ∂μ) ≤
      Real.sqrt (∫ x, h x ^ 2 ∂μ) * Real.sqrt (μ.real s) := by
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two h_nonneg
    (show 0 ≤ᵐ[μ] s.indicator (fun _ : X => (1 : ℝ)) from
      Filter.Eventually.of_forall (fun x => by
        change 0 ≤ s.indicator (fun _ : X => (1 : ℝ)) x
        by_cases hx : x ∈ s <;> simp [hx]))
    (by simpa using hh) (by simpa using (MemLp.indicator hs (memLp_const (1 : ℝ))))
  have hmul : (fun x => h x * s.indicator (fun _ : X => (1 : ℝ)) x) =
      s.indicator h := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  have hpow : (fun x => (s.indicator (fun _ : X => (1 : ℝ)) x) ^ (2 : ℝ)) =
      s.indicator (fun _ : X => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hmul, integral_indicator hs, hpow] at hCS
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hCS
  have hmass : (∫ x, s.indicator (fun _ : X => (1 : ℝ)) x ∂μ) = μ.real s := by
    rw [integral_indicator hs]
    simp
  simpa only [hmass] using hCS

theorem withDensity_measureReal_le_sqrt
    (μ : Measure X) [IsFiniteMeasure μ] {h : X → ℝ}
    (hh : MemLp h 2 μ) (h_nonneg : 0 ≤ᵐ[μ] h)
    {s : Set X} (hs : MeasurableSet s) :
    (μ.withDensity (fun x => ENNReal.ofReal (h x))).real s ≤
      Real.sqrt (∫ x, h x ^ 2 ∂μ) * Real.sqrt (μ.real s) := by
  rw [measureReal_def, withDensity_apply _ hs]
  rw [← integral_eq_lintegral_of_nonneg_ae
    (ae_restrict_of_ae h_nonneg) hh.aestronglyMeasurable.restrict]
  exact setIntegral_density_le_sqrt μ hh h_nonneg hs

end Invariant233.EndpointLoss

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FiniteUniformLaw
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace Invariant233.FiniteUniformLaw

theorem map_equiv {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).toMeasure.map e = (PMF.uniformOfFintype β).toMeasure := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton b)]
  have he : e ⁻¹' {b} = {e.symm b} := by
    ext a
    exact e.eq_symm_apply.symm
  rw [he, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_congr e]

theorem infinitePi_restrict_uniform {ι : Type*} (α : ι → Type*)
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)] (s : Finset ι) :
    (Measure.infinitePi (fun i => (PMF.uniformOfFintype (α i)).toMeasure)).map s.restrict =
      (PMF.uniformOfFintype ((i : s) → α i)).toMeasure := by
  rw [Measure.infinitePi_map_restrict]
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.pi_singleton]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_pi, Nat.cast_prod]
  symm
  apply ENNReal.prod_inv_distrib
  intro i hi j hj hij
  exact Or.inr (ENNReal.natCast_ne_top _)

end Invariant233.FiniteUniformLaw

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_L2UniformAbsoluteContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Invariant233.EndpointLoss

variable {X ι : Type*} [MeasurableSpace X]

theorem uniformlyAbsolutelyContinuous_of_uniform_sqrt_bound
    (μ : Measure X) [IsFiniteMeasure μ] (ν : ι → Measure X)
    (hfinite : ∀ i, IsFiniteMeasure (ν i)) (H : ℝ)
    (hbound : ∀ i A, MeasurableSet A → (ν i).real A ≤ H * Real.sqrt (μ.real A)) :
    UniformlyAbsolutelyContinuous μ ν := by
  intro ε hε
  have he : 0 < (ε : ℝ) := by exact_mod_cast hε
  have hB : 0 < |H| + 1 := by positivity
  have hd : 0 < (ε : ℝ) / (|H| + 1) := div_pos he hB
  refine ⟨⟨((ε : ℝ) / (|H| + 1)) ^ 2, sq_nonneg _⟩, ?_, ?_⟩
  · change 0 < ((ε : ℝ) / (|H| + 1)) ^ 2
    positivity
  · intro A hA hsmall i
    let := hfinite i
    have hreal : μ.real A < ((ε : ℝ) / (|H| + 1)) ^ 2 := by
      exact (ENNReal.toReal_lt_toReal (measure_ne_top μ A) ENNReal.coe_ne_top).2 hsmall
    have hsqrt : Real.sqrt (μ.real A) < (ε : ℝ) / (|H| + 1) := by
      have ht := Real.sqrt_lt_sqrt (measureReal_nonneg) hreal
      simpa only [Real.sqrt_sq hd.le] using ht
    have hH : H ≤ |H| + 1 := by linarith [le_abs_self H]
    have hν : (ν i).real A < (ε : ℝ) := calc
      (ν i).real A ≤ H * Real.sqrt (μ.real A) := hbound i A hA
      _ ≤ (|H| + 1) * Real.sqrt (μ.real A) :=
        mul_le_mul_of_nonneg_right hH (Real.sqrt_nonneg _)
      _ < (|H| + 1) * ((ε : ℝ) / (|H| + 1)) :=
        mul_lt_mul_of_pos_left hsqrt hB
      _ = (ε : ℝ) := mul_div_cancel₀ _ hB.ne'
    exact (ENNReal.toReal_lt_toReal (measure_ne_top (ν i) A) ENNReal.coe_ne_top).1 hν

theorem uniformlyAbsolutelyContinuous_withDensity
    (μ : Measure X) [IsFiniteMeasure μ] (h : ι → X → ℝ)
    (hh : ∀ i, MemLp (h i) 2 μ) (hn : ∀ i, 0 ≤ᵐ[μ] h i) (H : ℝ)
    (hb : ∀ i, Real.sqrt (∫ x, h i x ^ 2 ∂μ) ≤ H) :
    UniformlyAbsolutelyContinuous μ
      (fun i => μ.withDensity (fun x => ENNReal.ofReal (h i x))) := by
  have hfin : ∀ i, IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (h i x))) :=
    fun i => isFiniteMeasure_withDensity_ofReal ((hh i).integrable (by norm_num)).2
  apply uniformlyAbsolutelyContinuous_of_uniform_sqrt_bound μ _ hfin H
  intro i A hA
  exact (withDensity_measureReal_le_sqrt μ (hh i) (hn i) hA).trans
    (mul_le_mul_of_nonneg_right (hb i) (Real.sqrt_nonneg _))

theorem uniformlyAbsolutelyContinuous_Lp_withDensity
    (μ : Measure X) [IsFiniteMeasure μ] (f : ι → Lp ℝ 2 μ)
    (hn : ∀ i, 0 ≤ᵐ[μ] (f i : X → ℝ)) (H : ℝ) (hb : ∀ i, ‖f i‖ ≤ H) :
    UniformlyAbsolutelyContinuous μ
      (fun i => μ.withDensity (fun x => ENNReal.ofReal (f i x))) := by
  apply uniformlyAbsolutelyContinuous_withDensity μ (fun i => f i) (fun i => Lp.memLp (f i)) hn H
  intro i
  simpa only [sqrt_integral_sq_eq_norm] using hb i

theorem uniformlyAbsolutelyContinuous_of_Lp_densities
    (μ : Measure X) [IsFiniteMeasure μ] (ν : ι → Measure X) (H : ℝ)
    (hν : ∀ i, ∃ f : Lp ℝ 2 μ, (0 ≤ᵐ[μ] (f : X → ℝ)) ∧
      ν i = μ.withDensity (fun x => ENNReal.ofReal (f x)) ∧ ‖f‖ ≤ H) :
    UniformlyAbsolutelyContinuous μ ν := by
  choose f hn heq hb using hν
  have hfun : ν = fun i => μ.withDensity (fun x => ENNReal.ofReal (f i x)) :=
    funext heq
  rw [hfun]
  exact uniformlyAbsolutelyContinuous_Lp_withDensity μ f hn H hb

end Invariant233.EndpointLoss

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_LimitLaw
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Invariant233

theorem map_eq_of_ae_limits_of_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ℕ → Ω → ℝ} {Y : ℕ → Ω' → ℝ} {Z : Ω → ℝ} {W : Ω' → ℝ}
    (hX : ∀ n, AEMeasurable (X n) μ) (hY : ∀ n, AEMeasurable (Y n) ν)
    (hZ : AEMeasurable Z μ) (hW : AEMeasurable W ν)
    (hXZ : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Z ω)))
    (hYW : ∀ᵐ ω ∂ν, Tendsto (fun n => Y n ω) atTop (𝓝 (W ω)))
    (hXY : ∀ n, μ.map (X n) = ν.map (Y n)) : μ.map Z = ν.map W := by
  have h₁ := tendstoInDistribution_of_ae_tendsto hX hZ hXZ
  have h₂ := tendstoInDistribution_of_ae_tendsto hY hW hYW
  have h₃ : TendstoInDistribution X atTop W (fun _ => μ) ν :=
    { forall_aemeasurable := hX
      aemeasurable_limit := hW
      tendsto := by simpa only [hXY] using h₂.tendsto }
  exact tendstoInDistribution_unique X h₁ h₃

end Invariant233

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

theorem map_quantize_uniform (q : ℕ) [NeZero q] :
    (volume.restrict (Ico (0 : ℝ) 1)).map (quantize q) =
      (PMF.uniformOfFintype (Fin q)).toMeasure := by
  apply Measure.ext_of_singleton
  intro a
  rw [map_quantize_singleton]
  simp

end Invariant233.UniformQuantization

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_DigitAveraging
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators

namespace Invariant233.DigitAveraging

theorem sq_integral_le_mass_mul_integral_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {u : Ω → ℝ} (hu : Integrable u μ)
    (hu2 : Integrable (fun x => u x ^ 2) μ) (hM : 0 < μ.real univ) :
    (∫ x, u x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, u x ^ 2 ∂μ := by
  let M := μ.real univ
  let A := ∫ x, u x ∂μ
  let a := A / M
  have ha : a * M = A := div_mul_cancel₀ A (ne_of_gt hM)
  have he : (∫ x, (u x - a) ^ 2 ∂μ) =
      (∫ x, u x ^ 2 ∂μ) - 2 * a * A + a ^ 2 * M := by
    have hlin : Integrable (fun x => 2 * a * u x) μ := hu.const_mul _
    have hconst : Integrable (fun _ : Ω => a ^ 2) μ := integrable_const _
    have hpoint : (fun x => (u x - a) ^ 2) =
        (fun x => u x ^ 2 - 2 * a * u x + a ^ 2) := by
      funext x
      ring
    rw [hpoint, integral_add (show Integrable (fun x => u x ^ 2 - 2 * a * u x) μ from hu2.sub hlin) hconst, integral_sub hu2 hlin,
      integral_const_mul, integral_const]
    simp only [smul_eq_mul, Measure.real, M, A]
    ring
  have hnonneg : 0 ≤ ∫ x, (u x - a) ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  rw [he, ← ha] at hnonneg
  have hb : a ^ 2 * M ≤ ∫ x, u x ^ 2 ∂μ := by nlinarith
  change A ^ 2 ≤ M * ∫ x, u x ^ 2 ∂μ
  calc
    A ^ 2 = (a * M) ^ 2 := congrArg (fun z : ℝ => z ^ 2) ha.symm
    _ = M * (a ^ 2 * M) := by ring
    _ ≤ M * ∫ x, u x ^ 2 ∂μ := mul_le_mul_of_nonneg_left hb hM.le

theorem sum_integral_fibers {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
    {μ : Measure Ω} {f : Ω → α} (hf : Measurable f)
    {u : Ω → ℝ} (hu : Integrable u μ) :
    (∑ a : α, ∫ x in {x | f x = a}, u x ∂μ) = ∫ x, u x ∂μ := by
  have hm : ∀ a : α, MeasurableSet {x | f x = a} :=
    fun a => hf (measurableSet_singleton a)
  have hd : Pairwise (fun a b : α => Disjoint {x | f x = a} {x | f x = b}) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro x hxa hxb
    exact hab (hxa.symm.trans hxb)
  have hcover : (⋃ a : α, {x | f x = a}) = univ := by
    ext x
    simp
  rw [← integral_iUnion_fintype hm hd (fun _ => hu.integrableOn), hcover,
    Measure.restrict_univ]

theorem digit_averaging_energy_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : ℕ} (hq : 0 < q) {f : Ω → Fin q} (hf : Measurable f)
    (hmass : ∀ a : Fin q, μ.real {x | f x = a} = 1 / (q : ℝ))
    {h : Ω → ℝ} (hh : MemLp h 2 μ) :
    (1 / (q : ℝ)) * ∑ a : Fin q,
      ((q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) - 1) ^ 2 ≤
      ∫ x, (h x - 1) ^ 2 ∂μ := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hhInt : Integrable h μ := hh.integrable (by norm_num)
  have hu : MemLp (fun x => h x - 1) 2 μ := hh.sub (memLp_const 1)
  have huInt : Integrable (fun x => h x - 1) μ := hu.integrable (by norm_num)
  have hu2Int := hu.integrable_sq
  have hlocal : ∀ a : Fin q,
      (1 / (q : ℝ)) * ((q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) - 1) ^ 2 ≤
      ∫ x in {x | f x = a}, (h x - 1) ^ 2 ∂μ := by
    intro a
    have hpos : 0 < (μ.restrict {x | f x = a}).real univ := by
      rw [measureReal_restrict_apply_univ, hmass]
      positivity
    have hcs := sq_integral_le_mass_mul_integral_sq
      huInt.restrict hu2Int.restrict hpos
    rw [measureReal_restrict_apply_univ, hmass] at hcs
    have he : (q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) - 1 =
        (q : ℝ) * (∫ x in {x | f x = a}, h x - 1 ∂μ) := by
      rw [integral_sub hhInt.restrict (integrable_const 1), setIntegral_const]
      simp only [smul_eq_mul, mul_one, hmass]
      field_simp
    rw [he]
    calc
      (1 / (q : ℝ)) * ((q : ℝ) * (∫ x in {x | f x = a}, h x - 1 ∂μ)) ^ 2 =
          (q : ℝ) * (∫ x in {x | f x = a}, h x - 1 ∂μ) ^ 2 := by field_simp
      _ ≤ (q : ℝ) * ((1 / (q : ℝ)) *
          (∫ x in {x | f x = a}, (h x - 1) ^ 2 ∂μ)) :=
        mul_le_mul_of_nonneg_left hcs hqR.le
      _ = ∫ x in {x | f x = a}, (h x - 1) ^ 2 ∂μ := by field_simp
  rw [Finset.mul_sum]
  exact (Finset.sum_le_sum (fun a _ => hlocal a)).trans_eq
    (sum_integral_fibers hf hu2Int)

theorem digit_average_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {q : ℕ} {f : Ω → Fin q} {h : Ω → ℝ}
    (hh : ∀ᵐ x ∂μ, 0 ≤ h x) (a : Fin q) :
    0 ≤ (q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) :=
  mul_nonneg (Nat.cast_nonneg q) (integral_nonneg_of_ae (ae_restrict_of_ae hh))

theorem digit_average_mean
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {q : ℕ} (hq : 0 < q) {f : Ω → Fin q} (hf : Measurable f)
    {h : Ω → ℝ} (hh : Integrable h μ) :
    (1 / (q : ℝ)) * ∑ a : Fin q,
      (q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) = ∫ x, h x ∂μ := by
  rw [← Finset.mul_sum, sum_integral_fibers hf hh]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  field_simp

theorem digit_average_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : ℕ} (hq : 0 < q) {f : Ω → Fin q}
    (hmass : ∀ a : Fin q, μ.real {x | f x = a} = 1 / (q : ℝ))
    {h : Ω → ℝ} (hh : Integrable h μ) {B : ℝ}
    (hB : ∀ᵐ x ∂μ, h x ≤ B) (a : Fin q) :
    (q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) ≤ B := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
  calc
    (q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) ≤
        (q : ℝ) * (∫ _x in {x | f x = a}, B ∂μ) :=
      mul_le_mul_of_nonneg_left
        (integral_mono_ae hh.restrict (integrable_const B) (ae_restrict_of_ae hB)) hqR.le
    _ = B := by
      rw [setIntegral_const, smul_eq_mul, hmass]
      field_simp

theorem map_withDensity_eq_digit_density
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : ℕ} (hq : 0 < q) {f : Ω → Fin q} (hf : Measurable f)
    (hmass : ∀ a : Fin q, μ.real {x | f x = a} = 1 / (q : ℝ))
    {h : Ω → ℝ} (hh : Integrable h μ) (hnonneg : ∀ᵐ x ∂μ, 0 ≤ h x) :
    (μ.withDensity (fun x => ENNReal.ofReal (h x))).map f =
      (μ.map f).withDensity (fun a => ENNReal.ofReal
        ((q : ℝ) * ∫ x in {x | f x = a}, h x ∂μ)) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
  apply Measure.ext_of_singleton
  intro a
  have hfiber : f ⁻¹' {a} = {x | f x = a} := by ext x; simp
  have hmeas : MeasurableSet {x | f x = a} := hf (measurableSet_singleton a)
  have hmapa : (μ.map f) {a} = ENNReal.ofReal (1 / (q : ℝ)) := by
    rw [Measure.map_apply hf (measurableSet_singleton a), hfiber]
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ {x | f x = a})]
    exact congrArg ENNReal.ofReal (hmass a)
  rw [Measure.map_apply hf (measurableSet_singleton a), hfiber,
    withDensity_apply _ hmeas,
    withDensity_apply _ (measurableSet_singleton a), lintegral_singleton, hmapa,
    ← ofReal_integral_eq_lintegral_ofReal hh.restrict (ae_restrict_of_ae hnonneg)]
  rw [← ENNReal.ofReal_mul (digit_average_nonneg hnonneg a)]
  congr 1
  field_simp

theorem integral_map_eq_uniform_sum
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : ℕ} {f : Ω → Fin q} (hf : Measurable f)
    (hmass : ∀ a : Fin q, μ.real {x | f x = a} = 1 / (q : ℝ))
    (g : Fin q → ℝ) :
    (∫ a, g a ∂μ.map f) = (1 / (q : ℝ)) * ∑ a : Fin q, g a := by
  have hg : Integrable g (μ.map f) := by
    exact Integrable.of_finite
  rw [integral_fintype hg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hmap : (μ.map f).real {a} = μ.real {x | f x = a} := by
    unfold Measure.real
    rw [Measure.map_apply hf (measurableSet_singleton a)]
    congr 1
  rw [smul_eq_mul, hmap, hmass]

theorem integral_digit_energy_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : ℕ} (hq : 0 < q) {f : Ω → Fin q} (hf : Measurable f)
    (hmass : ∀ a : Fin q, μ.real {x | f x = a} = 1 / (q : ℝ))
    {h : Ω → ℝ} (hh : MemLp h 2 μ) :
    (∫ a, ((q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) - 1) ^ 2 ∂μ.map f) ≤
      ∫ x, (h x - 1) ^ 2 ∂μ := by
  rw [integral_map_eq_uniform_sum hf hmass]
  exact digit_averaging_energy_le hq hf hmass hh

end Invariant233.DigitAveraging

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_QuantizedDensity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.UniformQuantization

local instance instIsProbabilityMeasureRealRestrictVolumeIcoOfNat_solutions : IsProbabilityMeasure (volume.restrict (Ico (0 : ℝ) 1)) :=
  ⟨by simp⟩

theorem quantize_fiber_mass (q : ℕ) [NeZero q] (a : Fin q) :
    (volume.restrict (Ico (0 : ℝ) 1)).real {x | quantize q x = a} =
      1 / (q : ℝ) := by
  have hmass := map_quantize_singleton q a
  rw [Measure.map_apply (measurable_quantize q) (measurableSet_singleton a)] at hmass
  unfold Measure.real
  rw [show (volume.restrict (Ico (0 : ℝ) 1)) {x | quantize q x = a} =
      (q : ℝ≥0∞)⁻¹ from hmass]
  simp [one_div]

theorem map_withDensity_quantize (q : ℕ) [NeZero q] {h : ℝ → ℝ}
    (hh : Integrable h (volume.restrict (Ico (0 : ℝ) 1)))
    (hnonneg : ∀ᵐ x ∂volume.restrict (Ico (0 : ℝ) 1), 0 ≤ h x) :
    ((volume.restrict (Ico (0 : ℝ) 1)).withDensity (fun x => ENNReal.ofReal (h x))).map
      (quantize q) =
      (PMF.uniformOfFintype (Fin q)).toMeasure.withDensity
        (fun a => ENNReal.ofReal (binAverage q h a)) := by
  simpa only [map_quantize_uniform, binAverage] using
    DigitAveraging.map_withDensity_eq_digit_density (Nat.pos_of_ne_zero (NeZero.ne q))
      (measurable_quantize q) (quantize_fiber_mass q) hh hnonneg

theorem integral_binAverage_energy_le (q : ℕ) [NeZero q] {h : ℝ → ℝ}
    (hh : MemLp h 2 (volume.restrict (Ico (0 : ℝ) 1))) :
    (∫ a, (binAverage q h a - 1) ^ 2 ∂(PMF.uniformOfFintype (Fin q)).toMeasure) ≤
      ∫ x, (h x - 1) ^ 2 ∂volume.restrict (Ico (0 : ℝ) 1) := by
  simpa only [map_quantize_uniform, binAverage] using
    DigitAveraging.integral_digit_energy_le (Nat.pos_of_ne_zero (NeZero.ne q))
      (measurable_quantize q) (quantize_fiber_mass q) hh

theorem binAverage_nonneg (q : ℕ) [NeZero q] {h : ℝ → ℝ}
    (hh : ∀ᵐ x ∂volume.restrict (Ico (0 : ℝ) 1), 0 ≤ h x) (a : Fin q) :
    0 ≤ binAverage q h a := DigitAveraging.digit_average_nonneg hh a

theorem integral_binAverage (q : ℕ) [NeZero q] {h : ℝ → ℝ}
    (hh : Integrable h (volume.restrict (Ico (0 : ℝ) 1))) :
    (∫ a, binAverage q h a ∂(PMF.uniformOfFintype (Fin q)).toMeasure) =
      ∫ x, h x ∂volume.restrict (Ico (0 : ℝ) 1) := by
  rw [← map_quantize_uniform q,
    DigitAveraging.integral_map_eq_uniform_sum (measurable_quantize q) (quantize_fiber_mass q)]
  exact DigitAveraging.digit_average_mean (Nat.pos_of_ne_zero (NeZero.ne q))
    (measurable_quantize q) hh

theorem binAverage_le (q : ℕ) [NeZero q] {h : ℝ → ℝ} {B : ℝ}
    (hh : Integrable h (volume.restrict (Ico (0 : ℝ) 1)))
    (hB : ∀ᵐ x ∂volume.restrict (Ico (0 : ℝ) 1), h x ≤ B) (a : Fin q) :
    binAverage q h a ≤ B :=
  DigitAveraging.digit_average_le (Nat.pos_of_ne_zero (NeZero.ne q))
    (quantize_fiber_mass q) hh hB a

end Invariant233.UniformQuantization

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_SimultaneousLusin
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Topology
open scoped ENNReal

namespace Invariant233.SimultaneousLusin

theorem continuousOn_of_finer_compact {X Y : Type*}
    [t : TopologicalSpace X] [hT2 : T2Space X] [TopologicalSpace Y]
    {t' : TopologicalSpace X} (hle : t' ≤ t)
    {K : Set X} (hK : @IsCompact X t' K) {f : X → Y}
    (hf : @Continuous X Y t' _ f) : @ContinuousOn X Y t _ f K := by
  apply (@continuousOn_iff_isClosed X Y t _ f K).2
  intro s hs
  have hC : @IsCompact X t' (K ∩ f ⁻¹' s) :=
    hK.inter_right (hs.preimage hf)
  have hC' : @IsCompact X t (K ∩ f ⁻¹' s) := by
    simpa only [image_id] using
      (@IsCompact.image X X t' t (K ∩ f ⁻¹' s) id hC (continuous_id_of_le hle))
  exact ⟨K ∩ f ⁻¹' s, @IsCompact.isClosed X t hT2 _ hC',
    by ext x; simp [and_comm]⟩

theorem exists_compact_continuousOn {X Y : Type*}
    [t : TopologicalSpace X] [hPolish : PolishSpace X]
    [m : MeasurableSpace X] [hBorel : BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [SecondCountableTopology Y] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → Y} (hf : Measurable f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  obtain ⟨t', hle, hfc, hP'⟩ := hf.exists_continuous
  have hB' : @BorelSpace X t' m := by
    constructor
    exact hBorel.measurable_eq.trans
      (MeasureTheory.borel_eq_borel_of_le hP' hPolish hle).symm
  let : TopologicalSpace X := t'
  let : PolishSpace X := hP'
  let : BorelSpace X := hB'
  obtain ⟨K, -, hK, hsmall⟩ :=
    (MeasurableSet.univ : MeasurableSet (Set.univ : Set X)).exists_isCompact_sdiff_lt
      (measure_ne_top μ Set.univ) hε
  have hKold : @IsCompact X t K := by
    simpa only [image_id] using
      (@IsCompact.image X X t' t K id hK (continuous_id_of_le hle))
  refine ⟨K, hKold, ?_, ?_⟩
  · simpa only [← compl_eq_univ_sdiff] using hsmall
  · exact @continuousOn_of_finer_compact X Y t inferInstance _ t' hle K hK f hfc

end Invariant233.SimultaneousLusin

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_StrongContinuityFromColumns
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology

namespace Invariant233.StrongContinuityFromColumns

theorem continuous_apply_of_dense {𝕜 X E F : Type*}
    [NontriviallyNormedField 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C) {s : Set E} (hs : Dense s)
    (hcont : ∀ v ∈ s, Continuous (fun x => A x v)) (v : E) :
    Continuous (fun x => A x v) := by
  rw [continuous_iff_continuousAt]
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hden : 0 < 3 * (C + 1) := by positivity
  obtain ⟨w, hw, hvw⟩ := hs.exists_dist_lt v (div_pos hε hden)
  have hvw' : C * dist v w < ε / 3 := by
    have hdist : 0 ≤ dist v w := dist_nonneg
    have hlt : dist v w * (3 * (C + 1)) < ε :=
      (lt_div_iff₀ hden).mp hvw
    nlinarith
  have hevent : ∀ᶠ y in 𝓝 x, dist (A y w) (A x w) < ε / 3 :=
    Metric.tendsto_nhds.mp (hcont w hw).continuousAt (ε / 3) (by positivity)
  filter_upwards [hevent] with y hy
  have hleft : dist (A y v) (A y w) ≤ C * dist v w := by
    calc
      dist (A y v) (A y w) ≤ ‖A y‖ * dist v w := (A y).lipschitz.dist_le_mul v w
      _ ≤ C * dist v w := mul_le_mul_of_nonneg_right (hbound y) dist_nonneg
  have hright : dist (A x w) (A x v) ≤ C * dist v w := by
    calc
      dist (A x w) (A x v) ≤ ‖A x‖ * dist w v := (A x).lipschitz.dist_le_mul w v
      _ ≤ C * dist w v := mul_le_mul_of_nonneg_right (hbound x) dist_nonneg
      _ = C * dist v w := by rw [dist_comm w v]
  have htri := dist_triangle4 (A y v) (A y w) (A x w) (A x v)
  linarith

theorem continuous_apply_of_dense_span {𝕜 X E F ι : Type*}
    [NontriviallyNormedField 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C) (b : ι → E)
    (hb : (Submodule.span 𝕜 (Set.range b)).topologicalClosure = ⊤)
    (hcont : ∀ i, Continuous (fun x => A x (b i))) (v : E) :
    Continuous (fun x => A x v) := by
  apply continuous_apply_of_dense A hC hbound
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr hb) _ v
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      exact hcont i
  | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ : X => (0 : F)))
  | add w z hw hz hwc hzc =>
      simpa only [map_add, Pi.add_def] using hwc.add hzc
  | smul c w hw hwc =>
      simpa only [map_smul, Pi.smul_def] using hwc.const_smul c

theorem continuous_apply_of_hilbertBasis {𝕜 X E F ι : Type*}
    [RCLike 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C) (b : HilbertBasis ι 𝕜 E)
    (hcont : ∀ i, Continuous (fun x => A x (b i))) (v : E) :
    Continuous (fun x => A x v) :=
  continuous_apply_of_dense_span A hC hbound b b.dense_span hcont v

theorem continuousOn_apply_of_hilbertBasis {𝕜 X E F ι : Type*}
    [RCLike 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C) {Q : Set X}
    (hbound : ∀ x ∈ Q, ‖A x‖ ≤ C) (b : HilbertBasis ι 𝕜 E)
    (hcont : ∀ i, ContinuousOn (fun x => A x (b i)) Q) (v : E) :
    ContinuousOn (fun x => A x v) Q := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_apply_of_hilbertBasis (fun x : Q => A x) hC
    (fun x => hbound x x.property) b (fun i => (hcont i).domRestrict) v

end Invariant233.StrongContinuityFromColumns

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_StrongFieldContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection

open Filter Topology

variable {𝕜 E F G ι X : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable [TopologicalSpace X]

theorem strong_continuous_of_dense_of_bounded
    {A : X → E →L[𝕜] F} {s : Set E} {C : ℝ}
    (hs : Dense s) (hA : ∀ w ∈ s, Continuous (fun x => A x w))
    (hC : ∀ x, ‖A x‖ ≤ C) (v : E) :
    Continuous (fun x => A x v) := by
  apply continuous_of_uniform_approx_of_continuous
  intro u hu
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_uniformity_dist.mp hu
  let M : ℝ := max C 0 + 1
  have hM : 0 < M := by dsimp [M] <;> positivity
  obtain ⟨w, hw, hvw⟩ := hs.exists_dist_lt v (div_pos hε hM)
  refine ⟨(fun x => A x w), hA w hw, ?_⟩
  intro x
  apply hsub
  calc
    dist (A x v) (A x w) ≤ ‖A x‖ * dist v w := (A x).dist_le_opNorm v w
    _ ≤ M * dist v w := mul_le_mul_of_nonneg_right
      ((hC x).trans ((le_max_left C 0).trans (by dsimp [M]; exact le_add_of_nonneg_right zero_le_one)))
      (dist_nonneg)
    _ < ε := by simpa [mul_comm] using (lt_div_iff₀ hM).mp hvw

theorem strong_continuous_of_dense_span_of_bounded
    {A : X → E →L[𝕜] F} {b : ι → E} {C : ℝ}
    (hb : Dense (Submodule.span 𝕜 (Set.range b) : Set E))
    (hA : ∀ i, Continuous (fun x => A x (b i)))
    (hC : ∀ x, ‖A x‖ ≤ C) (v : E) :
    Continuous (fun x => A x v) := by
  apply strong_continuous_of_dense_of_bounded hb ?_ hC v
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      exact hA i
  | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ : X => (0 : F)))
  | add w z hw hz ihw ihz =>
      have h : Continuous (fun x => A x w + A x z) :=
        Continuous.add (f := fun x => A x w) (g := fun x => A x z) ihw ihz
      simpa only [map_add] using h
  | smul c w hw ihw =>
      have h : Continuous (fun x => c • A x w) :=
        Continuous.const_smul (g := fun x => A x w) ihw c
      simpa only [map_smul] using h

theorem strong_continuous_comp_of_bounded
    {A : X → F →L[𝕜] G} {B : X → E →L[𝕜] F} {C : ℝ}
    (hA : ∀ w, Continuous (fun x => A x w))
    (hB : ∀ v, Continuous (fun x => B x v))
    (hC : ∀ x, ‖A x‖ ≤ C) (v : E) :
    Continuous (fun x => ((A x).comp (B x)) v) := by
  exact continuous_apply_of_strong_continuous_of_bounded
    (A := A) (v := fun x => B x v) hA hC (hB v)

theorem isClosed_zero_set_of_strong_continuous
    {A : X → E →L[𝕜] F}
    (hA : ∀ v, Continuous (fun x => A x v)) :
    IsClosed {x | A x = 0} := by
  have heq : {x | A x = 0} = ⋂ v : E, {x | A x v = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hx v
      simp [hx]
    · intro hx
      ext v
      exact hx v
  rw [heq]
  exact isClosed_iInter fun v => isClosed_eq (hA v) continuous_const

end InvariantProjection

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_StrongLusin
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped ENNReal

namespace Invariant233.StrongLusin

theorem exists_compact_strong_and_continuousOn {𝕜 X E F ι J : Type*}
    {Y : J → Type*}
    [RCLike 𝕜] [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [∀ j, TopologicalSpace (Y j)] [∀ j, MeasurableSpace (Y j)]
    [∀ j, OpensMeasurableSpace (Y j)] [∀ j, SecondCountableTopology (Y j)]
    [Countable ι] [Countable J] (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C) (b : HilbertBasis ι 𝕜 E)
    (hcolumns : ∀ i, Measurable (fun x => A x (b i)))
    (g : ∀ j, X → Y j) (hg : ∀ j, Measurable (g j))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ Q : Set X, IsCompact Q ∧ μ Qᶜ < ε ∧
      (∀ v : E, ContinuousOn (fun x => A x v) Q) ∧
      ∀ j, ContinuousOn (g j) Q := by
  have hmeas : Measurable (fun x => ((fun i => A x (b i)), (fun j => g j x))) :=
    (Measurable.of_eval hcolumns).prodMk (Measurable.of_eval hg)
  obtain ⟨Q, hQ, hsmall, hcont⟩ :=
    SimultaneousLusin.exists_compact_continuousOn μ hmeas hε
  refine ⟨Q, hQ, hsmall, ?_, continuousOn_pi.mp hcont.snd⟩
  exact fun v => StrongContinuityFromColumns.continuousOn_apply_of_hilbertBasis A hC
    (fun x _ => hbound x) b (continuousOn_pi.mp hcont.fst) v

end Invariant233.StrongLusin

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_UniformAbsoluteContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal NNReal

namespace Invariant233.UniformlyAbsolutelyContinuous

variable {X ι : Type*} [MeasurableSpace X]

theorem absolutelyContinuous {μ : Measure X} {ν : ι → Measure X}
    (h : UniformlyAbsolutelyContinuous μ ν) (i : ι) : ν i ≪ μ := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hzero
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨δ, hδ, hbound⟩ := h ε hε
  have hsmall : μ s < (δ : ℝ≥0∞) := by
    rw [hzero]
    exact_mod_cast hδ
  simpa only [bot_eq_zero, zero_add] using (hbound s hs hsmall i).le

end Invariant233.UniformlyAbsolutelyContinuous

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleParameterBlocks
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.CircleParameterData

theorem block_index_unique (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) {j k i : ℕ}
    (hij : i ∈ p.block j) (hik : i ∈ p.block k) : j = k := by
  have hj := (p.mem_block_iff j i).mp hij
  have hk := (p.mem_block_iff k i).mp hik
  have hmono := (p.blockEnd_strictMono hm).monotone
  apply le_antisymm
  · by_contra h
    have hjk : k ≤ j - 1 := by omega
    have hd := hmono hjk
    omega
  · by_contra h
    have hjk : j ≤ k - 1 := by omega
    have hd := hmono hjk
    omega

end Invariant233.CircleParameterData

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

theorem ofDigits_eq_prefix_add_tail {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (N : ℕ) :
    ofDigits d = (∑ n ∈ Finset.range N, term d n) + ∑' n, term d (N + n) := by
  simpa only [ofDigits, Nat.add_comm] using
    ((summable_terms hr d).sum_add_tsum_nat_add N).symm

theorem abs_ofDigits_sub_ofDigits_le {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    {d e : Digits r} {N : ℕ} (hde : ∀ n < N, d n = e n) :
    |ofDigits d - ofDigits e| ≤ 1 / (denominator r N : ℝ) := by
  rw [ofDigits_eq_prefix_add_tail hr d N, ofDigits_eq_prefix_add_tail hr e N]
  have heq : (∑ n ∈ Finset.range N, term d n) = ∑ n ∈ Finset.range N, term e n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [term, hde n (Finset.mem_range.mp hn)]
  rw [heq, add_sub_add_left_eq_sub, abs_sub_le_iff]
  have hd0 : (0 : ℝ) ≤ ∑' n, term d (N + n) :=
    tsum_nonneg (fun n => term_nonneg d (N + n))
  have he0 : (0 : ℝ) ≤ ∑' n, term e (N + n) :=
    tsum_nonneg (fun n => term_nonneg e (N + n))
  constructor <;> linarith [tsum_tail_le hr d N, tsum_tail_le hr e N]

theorem reciprocal_denominator_tendsto_zero {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) :
    Tendsto (fun n => 1 / (denominator r n : ℝ)) atTop (𝓝 0) :=
  (summable_reciprocal_denominator hr).tendsto_atTop_zero

theorem tendsto_ofDigits_of_agree_prefix {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    (d : Digits r) (e : ℕ → Digits r) (hde : ∀ N n, n < N → e N n = d n) :
    Tendsto (fun N => ofDigits (e N)) atTop (𝓝 (ofDigits d)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (reciprocal_denominator_tendsto_zero hr)
  · intro N
    exact norm_nonneg _
  · intro N
    simpa only [Real.norm_eq_abs] using abs_ofDigits_sub_ofDigits_le
      (fun i => lt_of_lt_of_le (by decide : 0 < 2) (hr i)) (hde N)

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

theorem canonical_prefix_error {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    {x : ℝ} (hx : x ∈ Set.Ico 0 1) (N : ℕ) :
    0 ≤ x - (∑ n ∈ Finset.range N, term (canonicalDigits r hr x) n) ∧
    x - (∑ n ∈ Finset.range N, term (canonicalDigits r hr x) n) <
      1 / (denominator r N : ℝ) := by
  have hq : (0 : ℝ) < denominator r N := by exact_mod_cast denominator_pos hr N
  have hgrid := denominator_mul_prefix hr (canonicalDigits r hr x) N
  rw [prefixRank_canonicalDigits hr hx N] at hgrid
  have hlow := Nat.floor_le (mul_nonneg hq.le hx.1)
  have hhigh := Nat.lt_floor_add_one ((denominator r N : ℝ) * x)
  constructor
  · nlinarith
  · apply (lt_div_iff₀ hq).mpr
    nlinarith

theorem ofDigits_canonicalDigits {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    {x : ℝ} (hx : x ∈ Set.Ico 0 1) :
    ofDigits (canonicalDigits r (fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n)) x) = x := by
  let hp : ∀ n, 0 < r n := fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n)
  let d := canonicalDigits r hp x
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range N, term d n) atTop (𝓝 x) := by
    have hzero : Tendsto (fun N => x - ∑ n ∈ Finset.range N, term d n) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (reciprocal_denominator_tendsto_zero hr)
      · intro N; exact (canonical_prefix_error hp hx N).1
      · intro N; exact (canonical_prefix_error hp hx N).2.le
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).sub hzero
    simpa using h
  have hs := (summable_terms hp d).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hs hlim

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

@[simp] theorem hybrid_apply_lt {r : ℕ → ℕ} (d e : Digits r) {N n : ℕ} (hn : n < N) :
    hybrid d e N n = e n := ite_eq_left hn

theorem tailValue_hybrid {r : ℕ → ℕ} (d e : Digits r) (N : ℕ) :
    tailValue (hybrid d e N) N = tailValue d N := by
  unfold tailValue
  congr 1
  apply tsum_congr
  intro n
  simp [term]

theorem denominator_mul_hybrid_sub {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d e : Digits r) (N : ℕ) :
    (denominator r N : ℝ) * (ofDigits (hybrid d e N) - ofDigits d) =
      ((prefixRank (hybrid d e N) N : ℤ) - (prefixRank d N : ℤ) : ℤ) := by
  rw [mul_sub, denominator_mul_ofDigits hr (hybrid d e N) N,
    denominator_mul_ofDigits hr d N, tailValue_hybrid]
  push_cast
  ring

theorem hybrid_sub_eq_int_div {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d e : Digits r) (N : ℕ) :
    ∃ z : ℤ, ofDigits (hybrid d e N) - ofDigits d = (z : ℝ) / (denominator r N : ℝ) := by
  refine ⟨(prefixRank (hybrid d e N) N : ℤ) - (prefixRank d N : ℤ), ?_⟩
  have hq : (denominator r N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast denominator_pos hr N)
  apply (eq_div_iff hq).mpr
  simpa only [mul_comm] using denominator_mul_hybrid_sub hr d e N

theorem tendsto_ofDigits_hybrid {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) (d e : Digits r) :
    Tendsto (fun N => ofDigits (hybrid d e N)) atTop (𝓝 (ofDigits e)) := by
  apply tendsto_ofDigits_of_agree_prefix hr e (hybrid d e)
  intro N n hn
  exact hybrid_apply_lt d e hn

end Invariant233.MixedRadix

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

end Invariant233.CouplingMarginalBounds

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

lemma intervalDensity_memLp (a b : ℝ) (p : ℝ≥0∞) :
    MemLp (intervalDensity a b) p baseLaw :=
  uniformDensity_memLp measurableSet_Ico p

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

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleDigitCoupling
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixNonterminal
attribute [-instance] _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.MixedRadix.hybrid_apply_ge _root_.OAI.Invariant233.MixedRadix.hybrid_apply_lt
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

namespace MixedRadix

variable {r : ℕ → ℕ} [∀ n, NeZero (r n)]

theorem uniformDigit_singleton (n : ℕ) (a : Fin (r n)) :
    (PMF.uniformOfFintype (Fin (r n))).toMeasure {a} = (r n : ℝ≥0∞)⁻¹ := by
  simp

theorem ae_nonterminal_uniformDigits (hr : ∀ n, 2 ≤ r n) :
    ∀ᵐ d ∂Measure.infinitePi (fun n => (PMF.uniformOfFintype (Fin (r n))).toMeasure),
      Nonterminal d := by
  let s : (n : ℕ) → Set (Fin (r n)) := fun n => {a | ¬(a : ℕ) + 1 < r n}
  have hs (n : ℕ) : MeasurableSet (s n) := Set.toFinite (s n) |>.measurableSet
  have heq (n : ℕ) : s n = {⟨r n - 1, by have := hr n; omega⟩} := by
    ext a
    simp only [s, Set.mem_ofPred_eq, Set.mem_singleton_iff, Fin.ext_iff]
    have ha := a.isLt
    have h := hr n
    omega
  have hprob (n : ℕ) : (PMF.uniformOfFintype (Fin (r n))).toMeasure (s n) ≤
      (2 : ℝ≥0∞)⁻¹ := by
    rw [heq, uniformDigit_singleton]
    exact ENNReal.inv_le_inv.mpr (by exact_mod_cast hr n)
  have hnull := infinitePi_eventually_mem_null
    (fun n => (PMF.uniformOfFintype (Fin (r n))).toMeasure) s hs
    (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1) hprob
  rw [ae_iff]
  simpa only [Nonterminal, Set.mem_ofPred_eq, not_forall, not_exists, not_and, s] using hnull

end MixedRadix
end Invariant233

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

theorem measurePreserving_unitCircle :
    MeasurePreserving (fun x : ℝ => (x : AddCircle (1 : ℝ)))
      (volume.restrict (Set.Ico 0 1)) volume := by
  rw [restrict_Ico_eq_restrict_Ioc]
  simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0

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

theorem circleValue_measurePreserving {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    (μ : Measure (Digits r))
    (hlaw : μ.map ofDigits = volume.restrict (Set.Ico 0 1)) :
    MeasurePreserving (@circleValue r) μ volume := by
  exact measurePreserving_unitCircle.comp ⟨measurable_ofDigits hr, hlaw⟩

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_MixedRadixHybridLaw
attribute [-instance] _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Invariant233.HybridLaw

theorem tendsto_finiteMeasure_map_of_ae_tendsto
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (P : FiniteMeasure Ω) {f : ℕ → Ω → X} {g : Ω → X}
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hlim : ∀ᵐ ω ∂(P : Measure Ω),
      Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n => P.map (f n)) atTop (𝓝 (P.map g)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro φ
  simp only [FiniteMeasure.toMeasure_map]
  simp_rw [integral_map (hf _).aemeasurable φ.continuous.aestronglyMeasurable,
    integral_map hg.aemeasurable φ.continuous.aestronglyMeasurable]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
  · intro n
    exact (φ.continuous.measurable.comp (hf n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall fun ω => φ.norm_coe_le_norm (f n ω)
  · filter_upwards [hlim] with ω hω
    exact (φ.continuous.tendsto (g ω)).comp hω

end Invariant233.HybridLaw

namespace Invariant233.MixedRadix

theorem tendsto_circleValue_hybrid {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    (d e : Digits r) :
    Tendsto (fun N => circleValue (hybrid d e N)) atTop (𝓝 (circleValue e)) := by
  exact (AddCircle.continuous_mk' (1 : ℝ)).continuousAt.tendsto.comp
    (tendsto_ofDigits_hybrid hr d e)

theorem circleValue_hybrid_eq_add_int_div {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d e : Digits r) (N : ℕ) :
    ∃ z : ℤ, circleValue (hybrid d e N) = circleValue d +
      (((z : ℝ) / (denominator r N : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨z, hz⟩ := hybrid_sub_eq_int_div hr d e N
  refine ⟨z, ?_⟩
  have hreal : ofDigits (hybrid d e N) = ofDigits d +
      (z : ℝ) / (denominator r N : ℝ) := by linarith
  simpa only [circleValue, AddCircle.coe_add] using
    congrArg (fun x : ℝ => (x : AddCircle (1 : ℝ))) hreal

end Invariant233.MixedRadix

end

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

theorem floorCocycle_pos (p : CircleParameterData) (θ : ℝ) (k : ℤ) (x : Circle) :
    0 < p.floorCocycle θ k x := Real.exp_pos _

end CircleParameterData

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem measurable_parameter_cocycle (k : ℤ) : Measurable (p.floorCocycle θ k) :=
  CircleWeights.measurable_cocycle θ p.coordFrequency hp.coordFrequency_ne_zero
    p.coordCost k

end CircleParameterLaws
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleMarginalBudget
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233
namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

private theorem budgetBlocks_partition :
    ∀ i : ℕ, ∃! s : ℕ, i ∈ budgetBlocks p s := by
  intro i
  by_cases hi : i = 0
  · subst i
    refine ⟨0, by simp [budgetBlocks], ?_⟩
    intro s hs
    by_contra h
    have hb : 0 ∈ p.block s := by simpa [budgetBlocks, h] using hs
    have hb' := (p.mem_block_iff s 0).mp hb
    omega
  · obtain ⟨s, hs, his⟩ := p.exists_mem_block hp.m_pos i (by omega)
    have hs0 : s ≠ 0 := by omega
    refine ⟨s, by simpa [budgetBlocks, hs0] using his, ?_⟩
    intro t hit
    have ht0 : t ≠ 0 := by
      intro ht
      subst t
      simp [budgetBlocks, hi] at hit
    have ht : i ∈ p.block t := by simpa [budgetBlocks, ht0] using hit
    exact p.block_index_unique hp.m_pos ht his

theorem normalized_block_budget (a : ℕ → ℝ) (ha : ∀ s, 0 ≤ a s)
    (has : Summable a) :
    Summable (fun i : ℕ => if i = 0 then 0 else
      a (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ)) ∧
    (∑' i : ℕ, if i = 0 then 0 else
      a (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ)) ≤ ∑' s, a s := by
  classical
  let f : ℕ → ℝ := fun i => if i = 0 then 0 else
    a (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ)
  have hfnonneg : ∀ i, 0 ≤ f i := by
    intro i
    simp only [f]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (ha _) (Nat.cast_nonneg _)
  have hblock (s : ℕ) :
      (∑' i : budgetBlocks p s, f i) = if s = 0 then 0 else a s := by
    rw [Finset.tsum_subtype]
    by_cases hs : s = 0
    · subst s
      simp [budgetBlocks, f]
    · have hspos : 1 ≤ s := by omega
      rw [ite_eq_right hs]
      simp only [budgetBlocks, ite_eq_right hs]
      have hm : (p.m s : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos s hspos).ne'
      calc
        (∑ i ∈ p.block s, f i) = ∑ _i ∈ p.block s, a s / (p.m s : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi0 : i ≠ 0 := by
            have := (p.mem_block_iff s i).mp hi
            omega
          simp only [f, ite_eq_right hi0, p.blockIndex_eq_of_mem hp.m_pos hi]
        _ = a s := by
          simp only [Finset.sum_const, nsmul_eq_mul, p.card_block s hspos]
          field_simp
  have hgnonneg : ∀ s, 0 ≤ (if s = 0 then 0 else a s) := by
    intro s
    split_ifs
    · exact le_rfl
    · exact ha s
  have hgle : ∀ s, (if s = 0 then 0 else a s) ≤ a s := by
    intro s
    split_ifs
    · exact ha s
    · exact le_rfl
  have hgs : Summable (fun s : ℕ => if s = 0 then 0 else a s) :=
    Summable.of_nonneg_of_le hgnonneg hgle has
  have hfs : Summable f := by
    apply (summable_partition hfnonneg hp.budgetBlocks_partition).mpr
    constructor
    · intro s
      exact (hasSum_fintype _).summable
    · apply hgs.congr
      intro s
      exact (hblock s).symm
  refine ⟨hfs, ?_⟩
  let e := Set.sigmaEquiv (fun s => (budgetBlocks p s : Set ℕ)) hp.budgetBlocks_partition
  have he (z : Σ s, (budgetBlocks p s : Set ℕ)) : e z = z.2 := rfl
  have hsig : Summable (fun z : Σ s, (budgetBlocks p s : Set ℕ) => f z.2) := by
    apply (e.summable_iff.mpr hfs).congr
    intro z
    change f (e z) = f z.2
    rw [he]
  calc
    (∑' i, f i) = ∑' z : Σ s, (budgetBlocks p s : Set ℕ), f z.2 :=
      by simpa only [he] using (e.tsum_eq f).symm
    _ = ∑' s, ∑' i : budgetBlocks p s, f i := hsig.tsum_sigma
    _ = ∑' s, if s = 0 then 0 else a s := tsum_congr hblock
    _ ≤ ∑' s, a s := hgs.tsum_le_tsum hgle has

end CircleParameterLaws

namespace CircleParameterData

theorem summable_kappa_sq : Summable (fun s : ℕ => kappa s ^ 2) := by
  have h : Summable (fun s : ℕ => 1 / (s : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  apply (h.mul_left ((1 / 100 : ℝ) ^ 2)).congr
  intro s
  simp only [kappa, div_pow, mul_pow]
  ring

end CircleParameterData

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem circle_marginal_budget (j : ℕ) :
    Summable (fun i : ℕ => if i = 0 then 0 else
      50 * (CircleParameterData.kappa (p.blockIndex i) ^ 2 /
        (p.m (p.blockIndex i) : ℝ) +
        (if p.blockIndex i = j then 1 else 0) / (p.m (p.blockIndex i) : ℝ))) ∧
    (∑' i : ℕ, if i = 0 then 0 else
      50 * (CircleParameterData.kappa (p.blockIndex i) ^ 2 /
        (p.m (p.blockIndex i) : ℝ) +
        (if p.blockIndex i = j then 1 else 0) / (p.m (p.blockIndex i) : ℝ))) ≤
      50 * ((∑' s : ℕ, CircleParameterData.kappa s ^ 2) + 1) := by
  let a : ℕ → ℝ := fun s => 50 *
    (CircleParameterData.kappa s ^ 2 + if s = j then 1 else 0)
  have ha : ∀ s, 0 ≤ a s := by
    intro s
    dsimp [a]
    positivity
  have hs : Summable a :=
    (CircleParameterData.summable_kappa_sq.add (hasSum_ite_eq j (1 : ℝ)).summable).mul_left 50
  have heq : (fun i : ℕ => if i = 0 then 0 else
      50 * (CircleParameterData.kappa (p.blockIndex i) ^ 2 /
        (p.m (p.blockIndex i) : ℝ) +
        (if p.blockIndex i = j then 1 else 0) / (p.m (p.blockIndex i) : ℝ))) =
      (fun i : ℕ => if i = 0 then 0 else
        a (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ)) := by
    funext i
    dsimp [a]
    split_ifs <;> ring
  rw [heq]
  obtain ⟨hsum, hle⟩ := hp.normalized_block_budget a ha hs
  refine ⟨hsum, hle.trans_eq ?_⟩
  simp only [a, tsum_mul_left, Summable.tsum_add CircleParameterData.summable_kappa_sq
    (hasSum_ite_eq j (1 : ℝ)).summable, tsum_ite_eq]

end CircleParameterLaws
end Invariant233

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

end Invariant233.ProductDensity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleDigitEnergy
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

lemma endpointDensity_memLp (side : Bool) (m a b : ℝ) (l : Label) :
    MemLp (endpointDensity side m a b l) 2 baseLaw := by
  cases l with
  | none => exact memLp_const 1
  | some i => cases side <;> fin_cases i <;> exact intervalDensity_memLp _ _ 2

lemma marginalDensity_memLp (side : Bool) (κ m a b t : ℝ) :
    MemLp (marginalDensity side κ m a b t) 2 baseLaw := by
  apply (memLp_const (diagonalMass κ m a b t)).add
  exact memLp_finsetSum Finset.univ (fun i _ =>
    (endpointDensity_memLp side m a b (some i)).const_mul _)

lemma endpointDensity_integral {m a b : ℝ} (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4) (side : Bool) (l : Label) :
    (∫ x, endpointDensity side m a b l x ∂baseLaw) = 1 := by
  have := endpointLaw_isProbabilityMeasure hm ha ha' hb hb' side l
  have h := congrArg (fun ν : Measure ℝ => ν univ)
    (endpointLaw_eq_density hm ha ha' hb hb' side l)
  rw [measure_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
      ((endpointDensity_memLp side m a b l).integrable (by norm_num))
      (Filter.Eventually.of_forall (endpointDensity_nonneg side m a b l))] at h
  have hn : 0 ≤ ∫ x, endpointDensity side m a b l x ∂baseLaw :=
    integral_nonneg (endpointDensity_nonneg side m a b l)
  exact (ENNReal.ofReal_eq_ofReal_iff hn (by norm_num)).mp (by simpa using h.symm)

lemma marginalDensity_integral {κ m a b t : ℝ} (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4) (side : Bool) :
    (∫ x, marginalDensity side κ m a b t x ∂baseLaw) = 1 := by
  have hi (i : Fin 5) : Integrable
      (fun x => componentProbabilities κ m a b t i * endpointDensity side m a b (some i) x)
      baseLaw :=
    ((endpointDensity_memLp side m a b (some i)).integrable (by norm_num)).const_mul _
  unfold marginalDensity
  rw [integral_add (integrable_const _) (integrable_finsetSum Finset.univ (fun i _ => hi i)),
    integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul,
    endpointDensity_integral hm ha ha' hb hb' side, mul_one]
  simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, diagonalMass]
  ring

lemma marginalDensity_energy {κ m a b t : ℝ} (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) (side : Bool) :
    (∫ x, (marginalDensity side κ m a b t x - 1) ^ 2 ∂baseLaw) ≤
      50 * (κ ^ 2 / m + t / m) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hf (i : Fin 5) : MemLp
      (fun x => endpointDensity side m a b (some i) x - 1) 2 baseLaw :=
    (endpointDensity_memLp side m a b (some i)).sub (memLp_const 1)
  have hv (i : Fin 5) :
      (∫ x, (endpointDensity side m a b (some i) x - 1) ^ 2 ∂baseLaw) ≤
        componentVarianceBounds (2 * m) a b i := by
    cases side
    · exact leftDensity_variance_bound (by linarith) ha0 ha' hb0 hb' i
    · exact rightDensity_variance_bound (by linarith) ha0 ha' hb0 hb' i
  have hcs := integral_sq_weighted_sum_le hf (componentProbabilities κ m a b t)
  have hs : (∑ i, componentProbabilities κ m a b t i ^ 2 *
      ∫ x, (endpointDensity side m a b (some i) x - 1) ^ 2 ∂baseLaw) ≤
      ∑ i, componentProbabilities κ m a b t i ^ 2 *
        componentVarianceBounds (2 * m) a b i :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hv i) (sq_nonneg _))
  have he : (∑ i, componentProbabilities κ m a b t i ^ 2 *
      componentVarianceBounds (2 * m) a b i) = 8 * κ ^ 2 / m + 2 * t ^ 2 / m := by
    simp only [componentProbabilities, componentVarianceBounds, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    have hra := rho_sq_div_width (κ := κ) hm0 ha0
    have hrb := rho_sq_div_width (κ := κ) hm0 hb0
    have htag : (t / m) ^ 2 * (2 * m) = 2 * t ^ 2 / m := by field_simp
    rw [htag]
    simp only [div_eq_mul_inv] at hra hrb ⊢
    nlinarith
  have ht2 : t ^ 2 / m ≤ t / m :=
    div_le_div_of_nonneg_right (by nlinarith) hm0.le
  have hκ2 : 0 ≤ κ ^ 2 / m := div_nonneg (sq_nonneg _) hm0.le
  have htdiv : 0 ≤ t / m := div_nonneg ht0 hm0.le
  simp only [Fintype.card_fin] at hcs
  calc
    _ = ∫ x, (∑ i, componentProbabilities κ m a b t i *
        (endpointDensity side m a b (some i) x - 1)) ^ 2 ∂baseLaw := by
      congr 1
      funext x
      rw [marginalDensity, OneCoordinateCoupling.marginalDensity_sub_one]
    _ ≤ 5 * (∑ i, componentProbabilities κ m a b t i ^ 2 *
        componentVarianceBounds (2 * m) a b i) :=
      hcs.trans (mul_le_mul_of_nonneg_left hs (by norm_num))
    _ ≤ _ := by
      rw [he]
      simp only [div_eq_mul_inv] at ht2 hκ2 htdiv ⊢
      nlinarith

lemma rawLaw_map_endpoint {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) (side : Bool) :
    (rawLaw κ m a b t).map (endpoint side) =
      baseLaw.withDensity (fun x => ENNReal.ofReal (marginalDensity side κ m a b t x)) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hq0 : 0 ≤ diagonalMass κ m a b t :=
    (by norm_num : (0 : ℝ) ≤ 49 / 50).trans
      (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  cases side
  · change (rawLaw κ m a b t).map (Prod.fst ∘ Prod.snd) = _
    rw [← Measure.map_map measurable_fst measurable_snd]
    unfold rawLaw
    rw [labelledMixture_map_snd]
    exact mixture_fst_real_density baseLaw _ _ _ _
      (leftDensity (2 * m) a b) hq0 (componentProbabilities_nonneg hκ0 hm0 ht0)
      (fun i x => (leftDensity_bound (by linarith) ha0 ha' hb0 hb' i x).1)
      (fun i => by fin_cases i <;> exact intervalDensity_measurable _ _)
      (leftLaw_eq_withDensity (by linarith) ha0 ha' hb0 hb')
  · change (rawLaw κ m a b t).map (Prod.snd ∘ Prod.snd) = _
    rw [← Measure.map_map measurable_snd measurable_snd]
    unfold rawLaw
    rw [labelledMixture_map_snd]
    exact mixture_snd_real_density baseLaw _ _ _ _
      (rightDensity (2 * m) a b) hq0 (componentProbabilities_nonneg hκ0 hm0 ht0)
      (fun i x => (rightDensity_bound (by linarith) ha0 ha' hb0 hb' i x).1)
      (fun i => by fin_cases i <;> exact intervalDensity_measurable _ _)
      (rightLaw_eq_withDensity (by linarith) ha0 ha' hb0 hb')

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_FinitePrefixLaw
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped Classical

namespace Invariant233.FiniteUniformLaw

theorem infinitePi_fin_uniform (α : ℕ → Type*)
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)] (N : ℕ) :
    (Measure.infinitePi (fun i => (PMF.uniformOfFintype (α i)).toMeasure)).map
        (fun d (i : Fin N) => d i) =
      (PMF.uniformOfFintype ((i : Fin N) → α i)).toMeasure := by
  classical
  let e : (Finset.range N) ≃ Fin N :=
    { toFun := fun i => ⟨i.1, Finset.mem_range.mp i.2⟩
      invFun := fun i => ⟨i.1, Finset.mem_range.mpr i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E : ((i : Finset.range N) → α i) ≃ ((i : Fin N) → α i) :=
    Equiv.piCongrLeft (fun i : Fin N => α i) e
  have hcomp : (fun d (i : Fin N) => d i) =
      E ∘ (Finset.range N).restrict := by rfl
  rw [hcomp, ← Measure.map_map (measurable_of_finite E) (Finset.measurable_restrict _),
    infinitePi_restrict_uniform]
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_of_finite E) (measurableSet_singleton a)]
  have he : E ⁻¹' {a} = {E.symm a} := by
    ext b
    exact E.eq_symm_apply.symm
  rw [he, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [PMF.uniformOfFintype_apply]
  congr 2
  simp only [← Nat.card_eq_fintype_card]
  exact Nat.card_congr E

end Invariant233.FiniteUniformLaw

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixLaw
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.MixedRadix.hybrid_apply_ge _root_.OAI.Invariant233.MixedRadix.hybrid_apply_lt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators Classical

namespace Invariant233.MixedRadix

theorem measurable_prefix_sum (r : ℕ → ℕ) (N : ℕ) :
    Measurable (fun d : Digits r => ∑ n ∈ Finset.range N, term d n) := by
  apply Finset.measurable_sum
  intro n hn
  exact ((measurable_of_finite (fun a : Fin (r n) => (a : ℝ))).comp
    (measurable_pi_apply n)).div_const _

theorem tendsto_prefix_sum {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, term d n) atTop (𝓝 (ofDigits d)) :=
  (summable_terms hr d).hasSum.tendsto_sum_nat

theorem tendsto_quantized_prefix {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) :
    Tendsto (fun N => (⌊(denominator r N : ℝ) * x⌋₊ : ℝ) /
      (denominator r N : ℝ)) atTop (𝓝 x) := by
  let hp : ∀ n, 0 < r n := fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n)
  have heq : (fun N => (⌊(denominator r N : ℝ) * x⌋₊ : ℝ) /
      (denominator r N : ℝ)) =
      (fun N => ∑ n ∈ Finset.range N, term (canonicalDigits r hp x) n) := by
    funext N
    have hq : (denominator r N : ℝ) ≠ 0 :=
      ne_of_gt (by exact_mod_cast denominator_pos hp N)
    have h := denominator_mul_prefix hp (canonicalDigits r hp x) N
    rw [prefixRank_canonicalDigits hp hx N] at h
    exact (eq_div_iff hq).mpr (by simpa [mul_comm] using h) |>.symm
  rw [heq]
  have hrec : ofDigits (canonicalDigits r hp x) = x := ofDigits_canonicalDigits hr hx
  simpa only [hrec] using tendsto_prefix_sum hp (canonicalDigits r hp x)

theorem map_prefixRank_uniform (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) (N : ℕ) [NeZero (denominator r N)] :
    (digitLaw r hr).map
      (fun d => finitePrefixRankEquiv r hr N (fun i : Fin N => d i)) =
      (PMF.uniformOfFintype (Fin (denominator r N))).toMeasure := by
  let : ∀ n, NeZero (r n) := fun n => ⟨ne_of_gt (hr n)⟩
  let : NeZero (denominator r N) := ⟨ne_of_gt (denominator_pos hr N)⟩
  let E := finitePrefixRankEquiv r hr N
  have hp : (digitLaw r hr).map (fun d (i : Fin N) => d i) =
      (PMF.uniformOfFintype ((i : Fin N) → Fin (r i))).toMeasure := by
    unfold digitLaw
    exact FiniteUniformLaw.infinitePi_fin_uniform (fun n => Fin (r n)) N
  have hm : Measurable (fun d : Digits r => fun i : Fin N => d i) :=
    Measurable.of_eval (fun index => measurable_pi_apply (index : ℕ))
  change (digitLaw r hr).map (E ∘ (fun d (i : Fin N) => d i)) = _
  rw [← Measure.map_map (measurable_of_finite E) hm, hp]
  exact FiniteUniformLaw.map_equiv E

theorem prefix_sum_eq_normalized_rank (r : ℕ → ℕ) (hr : ∀ n, 0 < r n)
    (N : ℕ) (d : Digits r) :
    (∑ n ∈ Finset.range N, term d n) =
      ((finitePrefixRankEquiv r hr N (fun i : Fin N => d i) : ℕ) : ℝ) /
        (denominator r N : ℝ) := by
  rw [finitePrefixRankEquiv_val]
  have heq : prefixRank (extendPrefix r hr N (fun i : Fin N => d i)) N =
      prefixRank d N := by
    apply prefixRank_congr
    intro n hn
    simp [hn]
  rw [heq]
  have hq : (denominator r N : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast denominator_pos hr N)
  exact (eq_div_iff hq).mpr (by simpa [mul_comm] using denominator_mul_prefix hr d N)

theorem map_prefix_sum_eq_quantized (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) (N : ℕ) :
    (digitLaw r hr).map (fun d => ∑ n ∈ Finset.range N, term d n) =
      (volume.restrict (Ico (0 : ℝ) 1)).map
        (fun x => (⌊(denominator r N : ℝ) * x⌋₊ : ℝ) / (denominator r N : ℝ)) := by
  let : ∀ n, NeZero (r n) := fun n => ⟨ne_of_gt (hr n)⟩
  let : NeZero (denominator r N) := ⟨ne_of_gt (denominator_pos hr N)⟩
  let R : Digits r → Fin (denominator r N) :=
    fun d => finitePrefixRankEquiv r hr N (fun i : Fin N => d i)
  let g : Fin (denominator r N) → ℝ := fun a => (a : ℝ) / (denominator r N : ℝ)
  have hR : Measurable R := (measurable_of_finite (finitePrefixRankEquiv r hr N)).comp
    (Measurable.of_eval (fun index : Fin N => measurable_pi_apply (index : ℕ)))
  have hg : Measurable g := measurable_of_finite _
  have heq : (fun d => ∑ n ∈ Finset.range N, term d n) = g ∘ R := by
    funext d
    exact prefix_sum_eq_normalized_rank r hr N d
  rw [heq, ← Measure.map_map hg hR]
  have hRlaw : (digitLaw r hr).map R =
      (PMF.uniformOfFintype (Fin (denominator r N))).toMeasure :=
    map_prefixRank_uniform r hr N
  rw [hRlaw, ← UniformQuantization.map_quantize_uniform (denominator r N),
    Measure.map_map hg (UniformQuantization.measurable_quantize _)]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ico] with x hx
  have hq : (0 : ℝ) < denominator r N := by exact_mod_cast denominator_pos hr N
  have hfloor : ⌊(denominator r N : ℝ) * x⌋₊ < denominator r N :=
    (Nat.floor_lt (mul_nonneg hq.le hx.1)).mpr (by nlinarith [hx.2])
  simp [g, UniformQuantization.quantize, Nat.mod_eq_of_lt hfloor]

theorem map_ofDigits_eq_volume (r : ℕ → ℕ) (hr : ∀ n, 2 ≤ r n) :
    (digitLaw r (fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n))).map ofDigits =
      volume.restrict (Ico (0 : ℝ) 1) := by
  let hp : ∀ n, 0 < r n := fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n)
  let μ := digitLaw r hp
  let ν := (volume : Measure ℝ).restrict (Ico (0 : ℝ) 1)
  have : IsProbabilityMeasure ν := ⟨by simp [ν]⟩
  have : IsProbabilityMeasure μ := digitLaw_isProbability r hp
  have hX : ∀ N, AEMeasurable (fun d : Digits r => ∑ n ∈ Finset.range N, term d n) μ :=
    fun N => (measurable_prefix_sum r N).aemeasurable
  have hY : ∀ N, AEMeasurable
      (fun x : ℝ => (⌊(denominator r N : ℝ) * x⌋₊ : ℝ) / (denominator r N : ℝ)) ν := by
    intro N
    exact (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_const.mul measurable_id).nat_floor).div_const _).aemeasurable
  have hZ : AEMeasurable (ofDigits : Digits r → ℝ) μ :=
    (continuous_ofDigits hr).measurable.aemeasurable
  have hW : AEMeasurable (id : ℝ → ℝ) ν := measurable_id.aemeasurable
  have hXZ : ∀ᵐ d ∂μ, Tendsto (fun N => ∑ n ∈ Finset.range N, term d n)
      atTop (𝓝 (ofDigits d)) := Filter.Eventually.of_forall (tendsto_prefix_sum hp)
  have hYW : ∀ᵐ x ∂ν, Tendsto
      (fun N => (⌊(denominator r N : ℝ) * x⌋₊ : ℝ) / (denominator r N : ℝ))
      atTop (𝓝 (id x)) := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ico] with x hx
    exact tendsto_quantized_prefix hr hx
  have h := Invariant233.map_eq_of_ae_limits_of_map_eq hX hY hZ hW hXZ hYW
    (map_prefix_sum_eq_quantized r hp)
  simpa only [Measure.map_id] using h

end Invariant233.MixedRadix

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixHaarLaw
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.MixedRadix

theorem digitLaw_ae_nonterminal {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    (hp : ∀ n, 0 < r n) : ∀ᵐ d ∂digitLaw r hp, Nonterminal d := by
  let : ∀ n, NeZero (r n) := fun n => ⟨ne_of_gt (hp n)⟩
  simpa only [digitLaw] using ae_nonterminal_uniformDigits hr

theorem circleValue_measurePreserving_digitLaw {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n) :
    MeasurePreserving (@circleValue r) (digitLaw r hp) volume := by
  exact circleValue_measurePreserving hr (digitLaw r hp) (map_ofDigits_eq_volume r hr)

theorem map_circleValue_digitLaw {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n) :
    (digitLaw r hp).map circleValue = volume :=
  (circleValue_measurePreserving_digitLaw hr hp).map_eq

theorem ae_circleCanonical_circleValue {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n) :
    ∀ᵐ d ∂digitLaw r hp, circleCanonical r hp (circleValue d) = d := by
  filter_upwards [digitLaw_ae_nonterminal hr hp] with d hd
  exact circleCanonical_circleValue hp d hd

theorem map_circleCanonical_volume {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n) :
    (volume : Measure (AddCircle (1 : ℝ))).map (circleCanonical r hp) =
      digitLaw r hp :=
  DensityTransport.map_inverse_eq (measurable_circleValue hr)
    (measurable_circleCanonical r hp) (map_circleValue_digitLaw hr hp)
    (ae_circleCanonical_circleValue hr hp)

theorem circleCanonical_measurePreserving {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n) :
    MeasurePreserving (circleCanonical r hp) volume (digitLaw r hp) :=
  ⟨measurable_circleCanonical r hp, map_circleCanonical_volume hr hp⟩

theorem digitLaw_circle_density_transport_ae {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n)
    {h : Digits r → ℝ} (hh : AEMeasurable h (digitLaw r hp)) :
    ((digitLaw r hp).withDensity (fun d => ENNReal.ofReal (h d))).map circleValue =
      volume.withDensity (fun x : AddCircle (1 : ℝ) =>
        ENNReal.ofReal (h (circleCanonical r hp x))) ∧
    eLpNorm (h ∘ circleCanonical r hp) 2 volume = eLpNorm h 2 (digitLaw r hp) :=
  DensityTransport.real_density_transport_ae (measurable_circleValue hr)
    (measurable_circleCanonical r hp) (map_circleValue_digitLaw hr hp)
    (ae_circleCanonical_circleValue hr hp) hh

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleQuantizedMarginals
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
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

lemma digitReference_isProbabilityMeasure (p : CircleParameterData)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (i : ℕ) :
    IsProbabilityMeasure (digitReference p hr i) := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  unfold digitReference
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma rawDensity_memLp (p : CircleParameterData) (j : ℕ) (side : Bool) (i : ℕ) :
    MemLp (rawDensity p j side i) 2 baseLaw := by
  unfold rawDensity
  split_ifs
  · exact memLp_const 1
  · exact marginalDensity_memLp _ _ _ _ _ _

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma rawDensity_laws (j : ℕ) (side : Bool) (i : ℕ) :
    (∀ x, 0 ≤ rawDensity p j side i x ∧ rawDensity p j side i x ≤ 10) ∧
      (∫ x, rawDensity p j side i x ∂baseLaw) = 1 ∧
      (∫ x, (rawDensity p j side i x - 1) ^ 2 ∂baseLaw) ≤
        (if i = 0 then 0 else 50 *
          (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
            tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))) := by
  by_cases hi : i = 0
  · simp [rawDensity, hi]
  have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
  have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
    exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by have := hp.m_ge_200 _ hs; omega)
  have hκ := CircleParameterLaws.coupling_kappa_bounds _ hs
  have ha := hp.coupling_a_bounds _ hs
  have hb := hp.coupling_b_bounds _ hs
  have ht := tag_bounds j (p.blockIndex i)
  simp only [rawDensity, ite_eq_right hi]
  refine ⟨fun x => ?_, marginalDensity_integral hm ha.1 ha.2 hb.1 hb.2 side,
    marginalDensity_energy hm ha.1 ha.2 hb.1 hb.2 ht.1 ht.2 side⟩
  have hx := marginalDensity_bounds hκ.1 hκ.2 hm ha.1 ha.2 hb.1 hb.2 ht.1 ht.2 side x
  exact ⟨(by norm_num : (0 : ℝ) ≤ 49 / 50).trans hx.1, hx.2.2.le⟩

lemma coordinateLaw_map_endpoint (j : ℕ) (side : Bool) (i : ℕ) :
    (coordinateLaw p j i).map (endpoint side) =
      baseLaw.withDensity (fun x => ENNReal.ofReal (rawDensity p j side i x)) := by
  by_cases hi : i = 0
  · simp only [coordinateLaw, rawDensity, ite_eq_left hi]
    unfold initialLaw
    rw [Measure.map_map (by cases side; exact measurable_fst.comp measurable_snd; exact measurable_snd.comp measurable_snd)
      (show Measurable (fun x : ℝ => ((none : Label), (x, x))) from by fun_prop)]
    cases side <;> simp [endpoint, Function.comp_def]
  have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
  have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
    exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by have := hp.m_ge_200 _ hs; omega)
  have hκ := CircleParameterLaws.coupling_kappa_bounds _ hs
  have ha := hp.coupling_a_bounds _ hs
  have hb := hp.coupling_b_bounds _ hs
  have ht := tag_bounds j (p.blockIndex i)
  simpa only [coordinateLaw, rawDensity, ite_eq_right hi] using
    rawLaw_map_endpoint hκ.1 hκ.2 hm ha.1 ha.2 hb.1 hb.2 ht.1 ht.2 side

lemma observedDigit_density (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ) :
    (coordinateLaw p j i).map (observedDigit p hr side i) =
      (digitReference p hr i).withDensity
        (fun d => ENNReal.ofReal (digitDensity p hr j side i d)) := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  change (coordinateLaw p j i).map (UniformQuantization.quantize _ ∘ endpoint side) = _
  rw [← Measure.map_map (UniformQuantization.measurable_quantize _)
    (by cases side; exact measurable_fst.comp measurable_snd; exact measurable_snd.comp measurable_snd), coordinateLaw_map_endpoint hp]
  have hh := (rawDensity_memLp p j side i).integrable (by norm_num)
  have hn : ∀ᵐ x ∂baseLaw, 0 ≤ rawDensity p j side i x :=
    Filter.Eventually.of_forall (fun x => ((rawDensity_laws hp j side i).1 x).1)
  rw [baseLaw_eq_restrict] at hh hn ⊢
  exact UniformQuantization.map_withDensity_quantize _ hh hn

lemma digitDensity_laws (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ) :
    (∀ d, 0 ≤ digitDensity p hr j side i d ∧ digitDensity p hr j side i d ≤ 10) ∧
      (∫ d, digitDensity p hr j side i d ∂digitReference p hr i) = 1 ∧
      (∫ d, (digitDensity p hr j side i d - 1) ^ 2 ∂digitReference p hr i) ≤
        (if i = 0 then 0 else 50 *
          (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
            tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))) := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  have hraw := rawDensity_laws hp j side i
  have hh := rawDensity_memLp p j side i
  rw [baseLaw_eq_restrict] at hh hraw
  refine ⟨fun d => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact UniformQuantization.binAverage_nonneg _
      (Filter.Eventually.of_forall (fun x => (hraw.1 x).1)) d
  · exact UniformQuantization.binAverage_le _ (hh.integrable (by norm_num))
      (Filter.Eventually.of_forall (fun x => (hraw.1 x).2)) d
  · exact (UniformQuantization.integral_binAverage _ (hh.integrable (by norm_num))).trans hraw.2.1
  · exact (UniformQuantization.integral_binAverage_energy_le _ hh).trans hraw.2.2

lemma digitDensity_memLp (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ) :
    MemLp (digitDensity p hr j side i) 2 (digitReference p hr i) := by
  have := digitReference_isProbabilityMeasure p hr i
  exact memLp_of_bounded (Filter.Eventually.of_forall (digitDensity_laws hp j hr side i).1)
    (measurable_of_finite _).aestronglyMeasurable 2

omit hp in
lemma measurable_hybridDigits (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ε : ℕ → Bool) :
    Measurable (hybridDigits p hr ε) :=
  Measurable.of_eval (fun index => (measurable_observedDigit hr (ε index) index).comp
    (measurable_pi_apply index))

lemma measurable_hybridPoint (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ε : ℕ → Bool) :
    Measurable (hybridPoint p hr ε) :=
  (MixedRadix.measurable_circleValue
    (MixedRadix.radices_ge_two hp.q_pos hp.frequency_increasing hp.frequency_divisible)).comp
      (measurable_hybridDigits hr ε)

lemma map_hybridDigits (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ε : ℕ → Bool) :
    (law p j).map (hybridDigits p hr ε) =
      Measure.infinitePi (fun i => (digitReference p hr i).withDensity
        (fun d => ENNReal.ofReal (digitDensity p hr j (ε i) i d))) := by
  let := coordinateLaw_isProbabilityMeasure hp j
  change (Measure.infinitePi (coordinateLaw p j)).map
    (fun ω i => observedDigit p hr (ε i) i (ω i)) = _
  rw [Measure.infinitePi_map_pi (coordinateLaw p j) (fun i => measurable_observedDigit hr (ε i) i)]
  congr 1
  funext i
  exact observedDigit_density hp j hr (ε i) i

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleMarginalDensity
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleCoupling
open CircleParameterData

theorem hybrid_density_of_coordinate_budget {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ε : ℕ → Bool) {C : ℝ}
    (hsum : Summable (fun i : ℕ => if i = 0 then 0 else 50 *
      (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
        tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))))
    (hC : (∑' i : ℕ, if i = 0 then 0 else 50 *
      (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
        tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))) ≤ C) :
    ∃ H : Circle → ℝ, MemLp H 2 volume ∧ (0 ≤ᵐ[volume] H) ∧
      (∫ x, H x) = 1 ∧ eLpNorm H 2 volume ≤ ENNReal.ofReal (Real.exp (C / 2)) ∧
      (law p j).map (hybridPoint p hr ε) =
        volume.withDensity (fun x => ENNReal.ofReal (H x)) := by
  let : ∀ i, IsProbabilityMeasure (digitReference p hr i) :=
    digitReference_isProbabilityMeasure p hr
  have he (i : ℕ) := (digitDensity_laws hp j hr (ε i) i).2.2
  have hsE : Summable (fun i =>
      ∫ d, (digitDensity p hr j (ε i) i d - 1) ^ 2 ∂digitReference p hr i) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg (fun d => sq_nonneg _)) he hsum
  obtain ⟨H, hH, hnonneg, hmean, hnorm, hmeasure⟩ :=
    ProductDensity.exists_product_density
      (μ := fun i => digitReference p hr i)
      (h := fun i => digitDensity p hr j (ε i) i) (C := C)
      (fun i => digitDensity_memLp hp j hr (ε i) i)
      (fun i d => ((digitDensity_laws hp j hr (ε i) i).1 d).1)
      (fun i => (digitDensity_laws hp j hr (ε i) i).2.1)
      hsE ((hsE.tsum_le_tsum he hsum).trans hC)
  have htwo := MixedRadix.radices_ge_two hp.q_pos hp.frequency_increasing hp.frequency_divisible
  change MemLp H 2 (MixedRadix.digitLaw (MixedRadix.radices p.q) hr) at hH
  change (0 ≤ᵐ[MixedRadix.digitLaw (MixedRadix.radices p.q) hr] H) at hnonneg
  change (∫ d, H d ∂MixedRadix.digitLaw (MixedRadix.radices p.q) hr) = 1 at hmean
  change eLpNorm H 2 (MixedRadix.digitLaw (MixedRadix.radices p.q) hr) ≤ _ at hnorm
  change (MixedRadix.digitLaw (MixedRadix.radices p.q) hr).withDensity
    (fun d => ENNReal.ofReal (H d)) = _ at hmeasure
  let G : Circle → ℝ := H ∘ MixedRadix.circleCanonical (MixedRadix.radices p.q) hr
  have hcan := MixedRadix.circleCanonical_measurePreserving htwo hr
  have htransport := MixedRadix.digitLaw_circle_density_transport_ae htwo hr
    hH.aestronglyMeasurable.aemeasurable
  refine ⟨G, ?_, ?_, ?_, ?_, ?_⟩
  · exact hH.comp_measurePreserving hcan
  · change ∀ᵐ x ∂(volume : Measure Circle),
      0 ≤ H (MixedRadix.circleCanonical (MixedRadix.radices p.q) hr x)
    exact hcan.quasiMeasurePreserving.ae (p := fun d => 0 ≤ H d) hnonneg
  · have hHm : AEStronglyMeasurable H
        ((volume : Measure Circle).map (MixedRadix.circleCanonical (MixedRadix.radices p.q) hr)) := by
      rw [hcan.map_eq]
      exact hH.aestronglyMeasurable
    have hi := integral_map hcan.measurable.aemeasurable hHm
    rw [hcan.map_eq] at hi
    exact hi.symm.trans hmean
  · exact htransport.2.le.trans hnorm
  · change (law p j).map
      (MixedRadix.circleValue ∘ hybridDigits p hr ε) = _
    rw [← Measure.map_map (MixedRadix.measurable_circleValue htwo)
      (measurable_hybridDigits hr ε), map_hybridDigits hp, ← hmeasure]
    exact htransport.1

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleDigitMarginalLaws
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace Invariant233.CircleCoupling
open CircleParameterData

theorem digitMarginalLaws {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) : DigitMarginalLaws p hr := by
  refine ⟨Real.exp_pos _, fun j ε => ?_⟩
  obtain ⟨hs, hC⟩ := hp.circle_marginal_budget j
  have hs' : Summable (fun i : ℕ => if i = 0 then 0 else 50 *
      (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
        tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))) := by
    simpa only [tag] using hs
  have hC' : (∑' i : ℕ, if i = 0 then 0 else 50 *
      (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
        tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))) ≤
      50 * ((∑' s : ℕ, kappa s ^ 2) + 1) := by
    simpa only [tag] using hC
  have h := hybrid_density_of_coordinate_budget hp j hr ε hs' hC'
  have he : 50 * ((∑' s : ℕ, kappa s ^ 2) + 1) / 2 =
      25 * ((∑' s : ℕ, kappa s ^ 2) + 1) := by ring
  simpa only [marginalBound, he] using h

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingHybrid
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Invariant233.CircleCoupling
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

omit hp in
lemma finiteHybridPoint_eq (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (N : ℕ) (ω : Sample) :
    finiteHybridPoint p hr N ω = MixedRadix.circleValue
      (MixedRadix.hybrid (digits p hr false ω) (digits p hr true ω) (N + 1)) := by
  change MixedRadix.circleValue (hybridDigits p hr (finiteHybridChoice N) ω) = _
  congr 1
  funext i
  simp only [hybridDigits, finiteHybridChoice, MixedRadix.hybrid]
  by_cases hi : i < N + 1 <;> simp [hi, digits]

lemma measurable_finiteHybridPoint (hr : ∀ i, 0 < MixedRadix.radices p.q i) (N : ℕ) :
    Measurable (finiteHybridPoint p hr N) := measurable_hybridPoint hp hr _

lemma tendsto_finiteHybridPoint (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ω : Sample) :
    Tendsto (fun N => finiteHybridPoint p hr N ω) atTop (𝓝 (point p hr true ω)) := by
  simp_rw [finiteHybridPoint_eq]
  exact (MixedRadix.tendsto_circleValue_hybrid
    (MixedRadix.radices_ge_two hp.q_pos hp.frequency_increasing hp.frequency_divisible)
    (digits p hr false ω) (digits p hr true ω)).comp (tendsto_add_atTop_nat 1)

lemma uniformlyAbsolutelyContinuous_hybrids
    (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    UniformlyAbsolutelyContinuous circleMeasure
      (fun ε : ℕ → Bool => (law p j).map (hybridPoint p hr ε)) := by
  apply EndpointLoss.uniformlyAbsolutelyContinuous_of_Lp_densities
    circleMeasure _ marginalBound
  intro ε
  obtain ⟨H, hH, hn, _, hb, he⟩ := (digitMarginalLaws hp hr).2 j ε
  change MemLp H 2 circleMeasure at hH
  change (0 ≤ᵐ[circleMeasure] H) at hn
  change eLpNorm H 2 circleMeasure ≤ ENNReal.ofReal marginalBound at hb
  change (law p j).map (hybridPoint p hr ε) =
    circleMeasure.withDensity (fun x => ENNReal.ofReal (H x)) at he
  refine ⟨hH.toLp H, ?_, ?_, ?_⟩
  · filter_upwards [hH.coeFn_toLp, hn] with x hx hnx
    rwa [hx]
  · rw [he]
    apply withDensity_congr_ae
    filter_upwards [hH.coeFn_toLp] with x hx
    rw [hx]
  · rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hb

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_DiagonalContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.sequenceHilbertIntBorelSpace _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ENNReal lp

namespace Invariant233.SequenceHilbert

variable {I X : Type*}

theorem norm_diagonal_le (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) : ‖diagonal a C hC ha‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

theorem diagonal_congr (a b : I → ℂ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ i, ‖a i‖ ≤ C) (hb : ∀ i, ‖b i‖ ≤ D)
    (hab : ∀ i, a i = b i) : diagonal a C hC ha = diagonal b D hD hb := by
  ext v i
  simp only [diagonal_apply, hab]

theorem strong_continuous_diagonal [TopologicalSpace X]
    (a : X → I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x i, ‖a x i‖ ≤ C)
    (hc : ∀ i, Continuous (fun x => a x i)) (v : SequenceHilbert I) :
    Continuous (fun x => diagonal (a x) C hC (ha x) v) := by
  classical
  let b : HilbertBasis I ℂ (SequenceHilbert I) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hb : ∀ i, b i = lp.single 2 i (1 : ℂ) := fun _ => rfl
  apply InvariantProjection.strong_continuous_of_dense_span_of_bounded
    (b := b) (C := C)
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span) ?_
    (fun x => norm_diagonal_le (a x) C hC (ha x)) v
  intro i
  simpa only [hb, diagonal_single, mul_one, Function.comp_def,
    lp.singleContinuousLinearMap_apply] using
    (lp.singleContinuousLinearMap ℂ (fun _ : I => ℂ) 2 i).continuous.comp (hc i)

end Invariant233.SequenceHilbert

namespace Invariant233

variable {I X : Type*} [TopologicalSpace X]

theorem isClosed_diagonal_relation
    (p : X → SequenceHilbert I →L[ℂ] SequenceHilbert I)
    (d : (X × X) → I → ℂ) (B C : ℝ) (hB : 0 ≤ B)
    (hd : ∀ t i, ‖d t i‖ ≤ B)
    (hp : ∀ v, Continuous (fun x => p x v))
    (hdc : ∀ i, Continuous (fun t => d t i))
    (hpn : ∀ x, ‖p x‖ ≤ C) :
    IsClosed {t : X × X |
      (1 - p t.2).comp ((SequenceHilbert.diagonal (d t) B hB (hd t)).comp (p t.1)) = 0} := by
  apply InvariantProjection.isClosed_zero_set_of_strong_continuous
  intro v
  have hleft : ∀ w, Continuous (fun t : X × X => (1 - p t.2) w) := by
    intro w
    have h : Continuous (fun t : X × X => w - p t.2 w) :=
      continuous_const.sub ((hp w).comp continuous_snd)
    simpa using h
  have hleftn : ∀ t : X × X,
      ‖1 - p t.2‖ ≤ ‖(1 : SequenceHilbert I →L[ℂ] SequenceHilbert I)‖ + C := by
    intro t
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (hpn t.2))
  have hright : ∀ w, Continuous (fun t : X × X =>
      ((SequenceHilbert.diagonal (d t) B hB (hd t)).comp (p t.1)) w) := by
    intro w
    apply InvariantProjection.strong_continuous_comp_of_bounded
      (fun z => SequenceHilbert.strong_continuous_diagonal d B hB hd hdc z)
      (fun z => (hp z).comp continuous_fst)
      (fun t => SequenceHilbert.norm_diagonal_le (d t) B hB (hd t)) w
  exact InvariantProjection.strong_continuous_comp_of_bounded hleft hright hleftn v

theorem isCompact_diagonal_relation [CompactSpace X]
    (p : X → SequenceHilbert I →L[ℂ] SequenceHilbert I)
    (d : (X × X) → I → ℂ) (B C : ℝ) (hB : 0 ≤ B)
    (hd : ∀ t i, ‖d t i‖ ≤ B)
    (hp : ∀ v, Continuous (fun x => p x v))
    (hdc : ∀ i, Continuous (fun t => d t i))
    (hpn : ∀ x, ‖p x‖ ≤ C) :
    IsCompact {t : X × X |
      (1 - p t.2).comp ((SequenceHilbert.diagonal (d t) B hB (hd t)).comp (p t.1)) = 0} :=
  (isClosed_diagonal_relation p d B C hB hd hp hdc hpn).isCompact

theorem isCompact_diagonal_relation_on
    (Q : Set X) (hQ : IsCompact Q)
    (p : X → SequenceHilbert I →L[ℂ] SequenceHilbert I)
    (d : (X × X) → I → ℂ) (B C : ℝ) (hB : 0 ≤ B)
    (hd : ∀ t i, ‖d t i‖ ≤ B)
    (hp : ∀ v, ContinuousOn (fun x => p x v) Q)
    (hdc : ∀ i, ContinuousOn (fun t => d t i) (Q ×ˢ Q))
    (hpn : ∀ x, ‖p x‖ ≤ C) :
    IsCompact {t : X × X | t ∈ Q ×ˢ Q ∧
      (1 - p t.2).comp ((SequenceHilbert.diagonal (d t) B hB (hd t)).comp (p t.1)) = 0} := by
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  let f : Q × Q → X × X := fun t => ((t.1 : X), (t.2 : X))
  have hf : Continuous f :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  let pQ : Q → SequenceHilbert I →L[ℂ] SequenceHilbert I := fun x => p x
  let dQ : (Q × Q) → I → ℂ := fun t => d (f t)
  have hpQ : ∀ v, Continuous (fun x : Q => pQ x v) := fun v => (hp v).domRestrict
  have hdQ : ∀ i, Continuous (fun t : Q × Q => dQ t i) := by
    intro i
    exact (hdc i).comp_continuous hf (fun t => ⟨t.1.property, t.2.property⟩)
  have hS := isCompact_diagonal_relation pQ dQ B C hB
    (fun t i => hd (f t) i) hpQ hdQ (fun x => hpn x)
  have himage := hS.image hf
  convert himage using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  constructor
  · rintro ⟨ht, hzero⟩
    refine ⟨(⟨t.1, ht.1⟩, ⟨t.2, ht.2⟩), ?_, rfl⟩
    exact hzero
  · rintro ⟨q, hzero, rfl⟩
    exact ⟨⟨q.1.property, q.2.property⟩, hzero⟩

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_UnrestrictedDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.sequenceHilbertIntBorelSpace _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.SequenceHilbert

variable {I : Type*}

theorem boundedDiagonal_eq (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) : boundedDiagonal a = diagonal a C hC ha := by
  unfold boundedDiagonal
  split
  · rename_i h
    exact diagonal_congr a a h.choose C h.choose_spec.1 hC h.choose_spec.2 ha (fun _ => rfl)
  · rename_i h
    exact False.elim (h ⟨C, hC, ha⟩)

@[simp]
theorem boundedDiagonal_apply_of_bound (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) (v : SequenceHilbert I) (i : I) :
    boundedDiagonal a v i = a i * v i := by
  rw [boundedDiagonal_eq a C hC ha, diagonal_apply]

end Invariant233.SequenceHilbert

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_OperatorCompactTransfer
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal lp

noncomputable section
namespace Invariant233.CompactTransfer

local instance operatorCompactTransferSecondCountableTopology :
    SecondCountableTopology (SequenceHilbert ℤ) := by
  let b : HilbertBasis ℤ ℂ (SequenceHilbert ℤ) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hs := (Set.countable_range b).isSeparable.span (R := ℂ) |>.closure
  have : TopologicalSpace.SeparableSpace (SequenceHilbert ℤ) :=
    TopologicalSpace.isSeparable_univ_iff.mp (by
      simpa only [← Submodule.topologicalClosure_coe, b.dense_span, Submodule.top_coe] using hs)
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem uniform_marginal_budget {X ι : Type*}
    [MeasurableSpace X] (μ : Measure X) (νs : ι → Measure (X × X))
    (hfirst : UniformlyAbsolutelyContinuous μ (fun i => (νs i).map Prod.fst))
    (hsecond : UniformlyAbsolutelyContinuous μ (fun i => (νs i).map Prod.snd)) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
      ∀ A : Set X, MeasurableSet A → μ A < δ → ∀ i,
        νs i (A ×ˢ Set.univ) + νs i (Set.univ ×ˢ A) ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨δ₁, hδ₁, hfirst⟩ := hfirst (ε / 2) hhalf
  obtain ⟨δ₂, hδ₂, hsecond⟩ := hsecond (ε / 2) hhalf
  refine ⟨(min δ₁ δ₂ : ℝ≥0), ?_, ?_⟩
  · exact ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_min hδ₁ hδ₂))
  intro A hA hμ i
  have hμ₁ : μ A < (δ₁ : ℝ≥0∞) := hμ.trans_le (by exact_mod_cast min_le_left δ₁ δ₂)
  have hμ₂ : μ A < (δ₂ : ℝ≥0∞) := hμ.trans_le (by exact_mod_cast min_le_right δ₁ δ₂)
  have h₁ := hfirst A hA hμ₁ i
  have h₂ := hsecond A hA hμ₂ i
  rw [Measure.map_apply measurable_fst hA] at h₁
  rw [Measure.map_apply measurable_snd hA] at h₂
  have heq₁ : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set X) := by ext t; simp
  have heq₂ : Prod.snd ⁻¹' A = (Set.univ : Set X) ×ˢ A := by ext t; simp
  rw [heq₁] at h₁
  rw [heq₂] at h₂
  calc
    νs i (A ×ˢ Set.univ) + νs i (Set.univ ×ˢ A) ≤
        ((ε / 2 : ℝ≥0) : ℝ≥0∞) + ((ε / 2 : ℝ≥0) : ℝ≥0∞) :=
      add_le_add h₁.le h₂.le
    _ = ε := by rw [← ENNReal.coe_add, add_halves]

theorem capped_operator_relation_transfer {X ι : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (F : ℤ → X → ℝ) (hF : ∀ i x, 0 < F i x)
    (hFm : ∀ i, Measurable (F i))
    (hpm : ∀ i : ℤ, Measurable (fun x => p x (lp.single 2 i 1)))
    (C : ℝ) (hC : 0 ≤ C) (hpn : ∀ x, ‖p x‖ ≤ C)
    (B : ℝ) (hB : 0 ≤ B)
    {L : Filter ι} [L.NeBot] {ν : FiniteMeasure (X × X)}
    {νs : ι → FiniteMeasure (X × X)} (hν : Tendsto νs L (𝓝 ν))
    (hsmall : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
      ∀ A : Set X, MeasurableSet A → μ A < δ → ∀ i,
        (νs i : Measure (X × X)) (A ×ˢ Set.univ) +
        (νs i : Measure (X × X)) (Set.univ ×ˢ A) ≤ ε)
    (hzero : ∀ i, ∀ᵐ t ∂(νs i : Measure (X × X)),
      (1 - p t.2).comp ((cappedDiagonal F hF B hB t).comp (p t.1)) = 0) :
    ∀ᵐ t ∂(ν : Measure (X × X)),
      (1 - p t.2).comp ((cappedDiagonal F hF B hB t).comp (p t.1)) = 0 := by
  classical
  let b : HilbertBasis ℤ ℂ (SequenceHilbert ℤ) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hb : ∀ i, b i = lp.single 2 i (1 : ℂ) := fun i => (b.repr_symm_single i).symm
  apply ae_mem_of_closed_approximation hν
  intro ε hε
  obtain ⟨δ, hδ, hδsmall⟩ := hsmall ε hε
  obtain ⟨Q, hQ, hμQ, hpQ, hFQ⟩ :=
    StrongLusin.exists_compact_strong_and_continuousOn μ p hC hpn b
      (fun i => by simpa only [hb] using hpm i) F hFm hδ
  let S : Set (X × X) := {t | t ∈ Q ×ˢ Q ∧
    (1 - p t.2).comp ((cappedDiagonal F hF B hB t).comp (p t.1)) = 0}
  have hScompact : IsCompact S := by
    apply isCompact_diagonal_relation_on Q hQ p
      (fun t i => ((min B (F i t.2 / F i t.1) : ℝ) : ℂ)) B C hB
      (fun t i => ?_) hpQ (fun i => ?_) hpn
    · have hn : 0 ≤ min B (F i t.2 / F i t.1) :=
        le_min hB (div_nonneg (hF i t.2).le (hF i t.1).le)
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn] using
        (min_le_left B (F i t.2 / F i t.1))
    · exact continuousOn_capped_ratio (F i) Q (hFQ i)
        (fun x _ => (hF i x).ne') B
  refine ⟨S, hScompact.isClosed, fun _ ht => ht.2,
    Filter.Eventually.of_forall ?_⟩
  intro i
  have hsub : ∀ᵐ t ∂(νs i : Measure (X × X)), t ∈ Sᶜ → t ∈ (Q ×ˢ Q)ᶜ := by
    filter_upwards [hzero i] with t ht
    intro hbad hQpair
    exact hbad ⟨hQpair, ht⟩
  apply (measure_mono_ae hsub).trans
  rw [Set.compl_prod_eq_union]
  exact (measure_union_le _ _).trans
    (hδsmall Qᶜ hQ.isClosed.measurableSet.compl hμQ i)

theorem cappedDiagonal_eq_ratioDiagonal {X : Type*} (F : ℤ → X → ℝ)
    (hF : ∀ i x, 0 < F i x) (B : ℝ) (hB : 0 ≤ B) (t : X × X)
    (hcap : ∀ i, F i t.2 / F i t.1 ≤ B) :
    cappedDiagonal F hF B hB t = ratioDiagonal F t := by
  have hnorm : ∀ i, ‖((F i t.2 / F i t.1 : ℝ) : ℂ)‖ ≤ B := by
    intro i
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (hF i t.2).le (hF i t.1).le)] using hcap i
  unfold ratioDiagonal
  rw [SequenceHilbert.boundedDiagonal_eq _ B hB hnorm]
  apply SequenceHilbert.diagonal_congr
  intro i
  simp only [min_eq_right (hcap i)]

theorem compact_operator_transfer {X ι : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (hp : ∀ x, IsStarProjection (p x))
    (F : ℤ → X → ℝ) (hF : ∀ i x, 0 < F i x)
    (hFm : ∀ i, Measurable (F i))
    (hpm : ∀ i : ℤ, Measurable (fun x => p x (lp.single 2 i 1)))
    {L : Filter ι} [L.NeBot] {ν : FiniteMeasure (X × X)}
    {νs : ι → FiniteMeasure (X × X)} (hν : Tendsto νs L (𝓝 ν))
    (hfirst : UniformlyAbsolutelyContinuous μ
      (fun i => (νs i : Measure (X × X)).map Prod.fst))
    (hsecond : UniformlyAbsolutelyContinuous μ
      (fun i => (νs i : Measure (X × X)).map Prod.snd))
    (B : ℝ) (hB : 0 < B)
    (hcapn : ∀ i k, ∀ᵐ t ∂(νs i : Measure (X × X)), F k t.2 / F k t.1 ≤ B)
    (hcap : ∀ k, ∀ᵐ t ∂(ν : Measure (X × X)), F k t.2 / F k t.1 ≤ B)
    (hzero : ∀ i, ∀ᵐ t ∂(νs i : Measure (X × X)),
      (1 - p t.2).comp ((ratioDiagonal F t).comp (p t.1)) = 0) :
    ∀ᵐ t ∂(ν : Measure (X × X)),
      (1 - p t.2).comp ((ratioDiagonal F t).comp (p t.1)) = 0 := by
  have hsmall := uniform_marginal_budget μ
    (fun i => (νs i : Measure (X × X))) hfirst hsecond
  have hbounded : ∀ x, ‖p x‖ ≤ (1 : ℝ) :=
    fun x => IsStarProjection.norm_le (p x) (hp x)
  have hzerocap : ∀ i, ∀ᵐ t ∂(νs i : Measure (X × X)),
      (1 - p t.2).comp ((cappedDiagonal F hF B hB.le t).comp (p t.1)) = 0 := by
    intro i
    filter_upwards [ae_all_iff.mpr (hcapn i), hzero i] with t ht hz
    rwa [cappedDiagonal_eq_ratioDiagonal F hF B hB.le t ht]
  have hresult := capped_operator_relation_transfer μ p F hF hFm hpm
    1 zero_le_one hbounded B hB.le hν hsmall hzerocap
  filter_upwards [ae_all_iff.mpr hcap, hresult] with t ht hz
  rwa [cappedDiagonal_eq_ratioDiagonal F hF B hB.le t ht] at hz

end Invariant233.CompactTransfer

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleOrderedTransfer
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace Invariant233.CircleCoupling
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma hybridPairLaw_fst (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) (N : ℕ) :
    (hybridPairLaw hp j hr N : Measure (Circle × Circle)).map Prod.fst =
      (law p j).map (point p hr false) := by
  change ((law p j).map _).map Prod.fst = _
  rw [Measure.map_map measurable_fst
    ((measurable_point hp hr false).prodMk (measurable_finiteHybridPoint hp hr N))]
  rfl

lemma hybridPairLaw_snd (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) (N : ℕ) :
    (hybridPairLaw hp j hr N : Measure (Circle × Circle)).map Prod.snd =
      (law p j).map (finiteHybridPoint p hr N) := by
  change ((law p j).map _).map Prod.snd = _
  rw [Measure.map_map measurable_snd
    ((measurable_point hp hr false).prodMk (measurable_finiteHybridPoint hp hr N))]
  rfl

lemma tendsto_hybridPairLaw (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    Tendsto (hybridPairLaw hp j hr) atTop (𝓝 (endpointPairLaw hp j hr)) := by
  apply HybridLaw.tendsto_finiteMeasure_map_of_ae_tendsto
  · intro N
    exact (measurable_point hp hr false).prodMk (measurable_finiteHybridPoint hp hr N)
  · exact (measurable_point hp hr false).prodMk (measurable_point hp hr true)
  · exact Eventually.of_forall fun ω => tendsto_const_nhds.prodMk_nhds
      (tendsto_finiteHybridPoint hp hr ω)

lemma hybridPairLaw_uniform_fst (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    UniformlyAbsolutelyContinuous circleMeasure
      (fun N => (hybridPairLaw hp j hr N : Measure (Circle × Circle)).map Prod.fst) := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := uniformlyAbsolutelyContinuous_hybrids hp j hr ε hε
  refine ⟨δ, hδ, ?_⟩
  intro A hA hμ N
  change ((hybridPairLaw hp j hr N : Measure (Circle × Circle)).map Prod.fst) A < ε
  rw [hybridPairLaw_fst hp j hr N]
  exact hb A hA hμ (fun _ => false)

lemma hybridPairLaw_uniform_snd (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    UniformlyAbsolutelyContinuous circleMeasure
      (fun N => (hybridPairLaw hp j hr N : Measure (Circle × Circle)).map Prod.snd) := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := uniformlyAbsolutelyContinuous_hybrids hp j hr ε hε
  refine ⟨δ, hδ, ?_⟩
  intro A hA hμ N
  change ((hybridPairLaw hp j hr N : Measure (Circle × Circle)).map Prod.snd) A < ε
  rw [hybridPairLaw_snd hp j hr N]
  exact hb A hA hμ (finiteHybridChoice N)

lemma finiteHybrid_rational_graph (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (N : ℕ) (ω : Sample) :
    ∃ z : ℤ, finiteHybridPoint p hr N ω =
      point p hr false ω + p.rationalTranslation (N + 1) z := by
  rw [finiteHybridPoint_eq]
  have h := MixedRadix.circleValue_hybrid_eq_add_int_div hr
    (digits p hr false ω) (digits p hr true ω) (N + 1)
  simpa only [MixedRadix.denominator_radices hp.frequency_zero hp.frequency_divisible,
    rationalTranslation, point] using h

lemma ae_hybridPairLaw_graph (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) (N : ℕ) :
    ∀ᵐ z ∂(hybridPairLaw hp j hr N : Measure (Circle × Circle)),
      ∃ r : ℤ, z.2 = z.1 + p.rationalTranslation (N + 1) r := by
  change ∀ᵐ z ∂(law p j).map
    (fun ω => (point p hr false ω, finiteHybridPoint p hr N ω)), _
  apply (ae_map_iff
    ((measurable_point hp hr false).prodMk (measurable_finiteHybridPoint hp hr N)).aemeasurable ?_).mpr
  · exact Eventually.of_forall (finiteHybrid_rational_graph hp hr N)
  · simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun r =>
      measurableSet_eq_fun measurable_snd (measurable_fst.add measurable_const)

theorem orderedCouplingIdentities_of_rational_oai
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    (hF : ∀ x, IsStarProjection (F x))
    (hFm : ∀ k : ℤ, Measurable (fun x => F x (lp.single 2 k 1)))
    (hgraph : p.RationalGraphIdentities θ F) :
    OrderedCouplingIdentities p θ hr F := by
  intro j
  have hzero (N : ℕ) : ∀ᵐ z ∂(hybridPairLaw hp j hr N : Measure (Circle × Circle)),
      (1 - F z.2).comp ((ratioDiagonal (p.floorCocycle θ) z).comp (F z.1)) = 0 := by
    apply Fields.ae_pair_relation_of_countable_graphs
      (fun x y => (1 - F y).comp ((ratioDiagonal (p.floorCocycle θ) (x, y)).comp (F x)) = 0)
      (fun r : ℤ => fun x => x + p.rationalTranslation (N + 1) r)
      ((hybridPairLaw_uniform_fst hp j hr).absolutelyContinuous N)
    · intro r
      filter_upwards [hgraph] with x hx
      exact hx (N + 1) (by omega) r
    · exact ae_hybridPairLaw_graph hp j hr N
  have hlim := CompactTransfer.compact_operator_transfer circleMeasure F hF
    (p.floorCocycle θ) (fun k x => p.floorCocycle_pos θ k x)
    hp.measurable_parameter_cocycle hFm (tendsto_hybridPairLaw hp j hr)
    (hybridPairLaw_uniform_fst hp j hr) (hybridPairLaw_uniform_snd hp j hr)
    1 (by norm_num) (ae_hybridPairLaw_ratio_cap hp j hr)
    (ae_endpointPairLaw_ratio_cap hp j hr) hzero
  have hpull := ae_of_ae_map
    ((measurable_point hp hr false).prodMk (measurable_point hp hr true)).aemeasurable hlim
  filter_upwards [hpull, ae_endpoint_ratio_cap hp j hr] with ω hω hcap
  exact ⟨hω, hcap⟩

end Invariant233.CircleCoupling

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.CircleCoupling.orderedCouplingIdentities_of_rational_oai := @OAI.Invariant233.CircleCoupling.orderedCouplingIdentities_of_rational_oai
