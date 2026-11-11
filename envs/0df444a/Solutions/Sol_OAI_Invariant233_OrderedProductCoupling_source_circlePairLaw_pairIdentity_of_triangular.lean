-- Prove2me | solution 1 for OAI.Invariant233.OrderedProductCoupling.source_circlePairLaw_pairIdentity_of_triangular
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:31:43.636593+00:00
-- url     : https://prove2.me/submissions/376400fa-9d86-49b8-83b4-8d53fdc61eb1

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.UniformApproximation
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
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
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

lemma circleHybridEndpoint_measurable (ε : ℕ → Bool) :
    Measurable (circleHybridEndpoint ε) :=
  circleEndpoint_measurable.comp (hybridEndpoint_measurable ε)

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

theorem circlePairLaw_fst (P : Parameters) :
    (circlePairLaw P).map Prod.fst = (law P).map circleLeftEndpoint := by
  rw [circlePairLaw, Measure.map_map measurable_fst
    (circleLeftEndpoint_measurable.prodMk circleRightEndpoint_measurable)]
  rfl

theorem circlePairLaw_snd (P : Parameters) :
    (circlePairLaw P).map Prod.snd = (law P).map circleRightEndpoint := by
  rw [circlePairLaw, Measure.map_map measurable_snd
    (circleLeftEndpoint_measurable.prodMk circleRightEndpoint_measurable)]
  rfl

theorem circlePairLaw_ordered (P : Parameters) :
    ∀ᵐ xy ∂circlePairLaw P, ProductModel.Ordered xy.1 xy.2 := by
  have hm : MeasurableSet {xy : ProductModel.Base × ProductModel.Base |
      ProductModel.Ordered xy.1 xy.2} := by
    change MeasurableSet {xy : ProductModel.Base × ProductModel.Base |
      ∀ i, realEndpoint xy.1 i ≤ realEndpoint xy.2 i}
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le
      ((measurable_pi_apply i).comp (realEndpoint_measurable.comp measurable_fst))
      ((measurable_pi_apply i).comp (realEndpoint_measurable.comp measurable_snd))
  exact (ae_map_iff
    (circleLeftEndpoint_measurable.prodMk circleRightEndpoint_measurable).aemeasurable hm).2
    (ae_circle_endpoints_ordered P)

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSampling
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory Set
open scoped ENNReal Topology BigOperators

namespace Invariant233.ProductModel.Sampling

theorem triangularEvent_measurable (I : Finset ℕ) : MeasurableSet (triangularEvent I) := by
  unfold triangularEvent
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _hi
  exact measurableSet_lt
    (representative_measurable.comp ((measurable_pi_apply i).comp measurable_fst))
    (representative_measurable.comp ((measurable_pi_apply i).comp measurable_snd))

end Invariant233.ProductModel.Sampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_RealTriangularLaw
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter

namespace Invariant233.OrderedProductCoupling

lemma circlePairEndpoint_measurable : Measurable circlePairEndpoint :=
  circleEndpoint_measurable.prodMap circleEndpoint_measurable

lemma measurePreserving_circlePairEndpoint :
    MeasurePreserving circlePairEndpoint (baseMeasure.prod baseMeasure)
      (ProductModel.baseMeasure.prod ProductModel.baseMeasure) :=
  measurePreserving_circleEndpoint.prod measurePreserving_circleEndpoint

lemma realSelectedEndpoint_measurable (I : Finset ℕ) :
    Measurable (fun xz : Endpoint × Endpoint => realSelectedEndpoint I xz.1 xz.2) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i ∈ I
  · simpa [realSelectedEndpoint, hi, Function.comp_def] using
      (measurable_pi_apply i).comp measurable_snd
  · simpa [realSelectedEndpoint, hi, Function.comp_def] using
      (measurable_pi_apply i).comp measurable_fst

lemma circleEndpoint_realSelectedEndpoint (I : Finset ℕ) (x z : Endpoint) :
    circleEndpoint (realSelectedEndpoint I x z) =
      ProductModel.selectedEndpoint I (circleEndpoint x) (circleEndpoint z) := by
  funext i
  by_cases hi : i ∈ I <;>
    simp [circleEndpoint, realSelectedEndpoint, ProductModel.selectedEndpoint, hi]

lemma realTriangularEvent_ae_preimage (I : Finset ℕ) :
    realTriangularEvent I =ᵐ[baseMeasure.prod baseMeasure]
      circlePairEndpoint ⁻¹' ProductModel.triangularEvent I := by
  have hx : ∀ᵐ xz ∂baseMeasure.prod baseMeasure,
      realEndpoint (circleEndpoint xz.1) = xz.1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae ae_realEndpoint_circleEndpoint
  have hz : ∀ᵐ xz ∂baseMeasure.prod baseMeasure,
      realEndpoint (circleEndpoint xz.2) = xz.2 :=
    measurePreserving_snd.quasiMeasurePreserving.ae ae_realEndpoint_circleEndpoint
  filter_upwards [hx, hz] with xz hx hz
  change (∀ i ∈ I, xz.1 i < xz.2 i) =
    (∀ i ∈ I, realEndpoint (circleEndpoint xz.1) i < realEndpoint (circleEndpoint xz.2) i)
  rw [hx, hz]

lemma map_restrict_realTriangularEvent (I : Finset ℕ) :
    ((baseMeasure.prod baseMeasure).restrict (realTriangularEvent I)).map circlePairEndpoint =
      (ProductModel.baseMeasure.prod ProductModel.baseMeasure).restrict
        (ProductModel.triangularEvent I) := by
  rw [Measure.restrict_congr_set (realTriangularEvent_ae_preimage I),
    ← Measure.restrict_map circlePairEndpoint_measurable
      (ProductModel.Sampling.triangularEvent_measurable I),
    measurePreserving_circlePairEndpoint.map_eq]

theorem map_realTriangularLaw (I : Finset ℕ) :
    (realTriangularLaw I).map circlePairEndpoint = ProductModel.triangularLaw I := by
  have hm := measurable_fst.prodMk (realSelectedEndpoint_measurable I)
  rw [realTriangularLaw, Measure.map_map circlePairEndpoint_measurable hm]
  have hcomp : circlePairEndpoint ∘ (fun xz : Endpoint × Endpoint =>
      (xz.1, realSelectedEndpoint I xz.1 xz.2)) =
      (fun xz : ProductModel.EndpointPair =>
        (xz.1, ProductModel.selectedEndpoint I xz.1 xz.2)) ∘ circlePairEndpoint := by
    funext xz
    exact Prod.ext rfl (circleEndpoint_realSelectedEndpoint I xz.1 xz.2)
  rw [hcomp, ← Measure.map_map (ProductModel.Sampling.endpointMap_measurable I)
    circlePairEndpoint_measurable, map_restrict_realTriangularEvent]
  rfl

end Invariant233.OrderedProductCoupling

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
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_PrefixHybrid
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Invariant233.ProductModel

theorem continuous_prefixEndpoint (D : ℕ) :
    Continuous (fun xy : EndpointPair => prefixEndpoint D xy.1 xy.2) := by
  apply continuous_pi
  intro i
  by_cases hi : i < D
  · simpa only [prefixEndpoint_apply, ite_eq_left hi, Function.comp_def] using
      (continuous_apply i).comp continuous_snd
  · simpa only [prefixEndpoint_apply, ite_eq_right hi, Function.comp_def] using
      (continuous_apply i).comp continuous_fst

theorem continuous_prefixPair (D : ℕ) : Continuous (prefixPair D) :=
  continuous_fst.prodMk (continuous_prefixEndpoint D)

theorem measurable_prefixPair (D : ℕ) : Measurable (prefixPair D) :=
  Sampling.endpointMap_measurable (Finset.range D)

theorem tendsto_prefixEndpoint (x y : Base) :
    Tendsto (fun D => prefixEndpoint D x y) atTop (𝓝 y) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i] with D hD
  simp [prefixEndpoint_apply, hD]

theorem tendsto_prefixPair (xy : EndpointPair) :
    Tendsto (fun D => prefixPair D xy) atTop (𝓝 xy) :=
  tendsto_const_nhds.prodMk_nhds (tendsto_prefixEndpoint xy.1 xy.2)

theorem prefixPairLaw_first_marginal (ν : Measure EndpointPair) (D : ℕ) :
    (prefixPairLaw ν D).map Prod.fst = ν.map Prod.fst := by
  rw [prefixPairLaw, Measure.map_map measurable_fst (measurable_prefixPair D)]
  rfl

theorem prefixPairLaw_weaklyConverges (ν : Measure EndpointPair) [IsFiniteMeasure ν] :
    WeaklyConverges (prefixPairLaw ν) ν := by
  intro φ
  have hmap (D : ℕ) :
      (∫ xy, φ xy ∂prefixPairLaw ν D) = ∫ xy, φ (prefixPair D xy) ∂ν := by
    exact integral_map (measurable_prefixPair D).aemeasurable
      φ.continuous.aestronglyMeasurable
  simp_rw [hmap]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
  · intro D
    exact (φ.continuous.comp (continuous_prefixPair D)).aestronglyMeasurable
  · exact integrable_const _
  · intro D
    exact Filter.Eventually.of_forall (fun xy => φ.norm_coe_le_norm (prefixPair D xy))
  · exact Filter.Eventually.of_forall (fun xy =>
      φ.continuous.continuousAt.tendsto.comp (tendsto_prefixPair xy))

theorem ordered_selectedEndpoint {x y : Base} (hxy : Ordered x y) (I : Finset ℕ) :
    Ordered x (selectedEndpoint I x y) ∧ Ordered (selectedEndpoint I x y) y := by
  constructor <;> intro i <;> by_cases hi : i ∈ I
  · simpa only [selectedEndpoint, ite_eq_left hi] using hxy i
  · simp only [selectedEndpoint, ite_eq_right hi, le_refl]
  · simp only [selectedEndpoint, ite_eq_left hi, le_refl]
  · simpa only [selectedEndpoint, ite_eq_right hi] using hxy i

end Invariant233.ProductModel

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

theorem measurable_cocycleVersion {I : Type*} [Countable I]
    (θ c : I → ℝ) (k : ℤ) : Measurable (cocycleVersion θ c k) := by
  apply Real.measurable_exp.comp
  apply Measurable.neg
  apply Measurable.tsum
  intro i
  have hrep : Measurable (fun x : Space I ↦ representative (x i)) :=
    measurable_representative.comp (measurable_pi_apply i)
  exact measurable_const.mul ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
    ((hrep.add_const ((k : ℝ) * θ i)).floor))

theorem cocycleVersion_pos {I : Type*} (θ c : I → ℝ) (k : ℤ) (x : Space I) :
    0 < cocycleVersion θ c k x :=
  Real.exp_pos _

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
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_PrefixCocycleCap
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Function Set

namespace Invariant233.ProductModel

theorem finite_floor_support_selectedEndpoint
    (θ : ℕ → ℝ) (k : ℤ) (x y : Base) (I : Finset ℕ)
    (hx : HasFiniteSupport (fun i =>
      ⌊circleRepresentative (x i) + (k : ℝ) * θ i⌋))
    (hy : HasFiniteSupport (fun i =>
      ⌊circleRepresentative (y i) + (k : ℝ) * θ i⌋)) :
    HasFiniteSupport (fun i =>
      ⌊circleRepresentative (selectedEndpoint I x y i) + (k : ℝ) * θ i⌋) := by
  apply (hx.union hy).subset
  intro i hi
  by_cases hI : i ∈ I
  · right
    simpa only [Function.mem_support, selectedEndpoint, ite_eq_left hI] using hi
  · left
    simpa only [Function.mem_support, selectedEndpoint, ite_eq_right hI] using hi

theorem ae_pair_all_int_finite_floor_support
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (ν : Measure EndpointPair)
    (hfst : ν.map Prod.fst ≪ baseMeasure)
    (hsnd : ν.map Prod.snd ≪ baseMeasure) :
    ∀ᵐ xy ∂ν, ∀ k : ℤ,
      HasFiniteSupport (fun i =>
        ⌊circleRepresentative (xy.1 i) + (k : ℝ) * θ i⌋) ∧
      HasFiniteSupport (fun i =>
        ⌊circleRepresentative (xy.2 i) + (k : ℝ) * θ i⌋) := by
  have hbase : ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      HasFiniteSupport (fun i =>
        ⌊circleRepresentative (x i) + (k : ℝ) * θ i⌋) :=
    CocycleSupport.ae_product_all_int_finite_floor_support θ hθ0 hθ
  have hx := ae_of_ae_map measurable_fst.aemeasurable (hfst.ae_le hbase)
  have hy := ae_of_ae_map measurable_snd.aemeasurable (hsnd.ae_le hbase)
  filter_upwards [hx, hy] with xy hx hy
  exact fun k => ⟨hx k, hy k⟩

theorem ae_ordered_cocycle_ratio_cap
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (ν : Measure EndpointPair)
    (hfst : ν.map Prod.fst ≪ baseMeasure)
    (hsnd : ν.map Prod.snd ≪ baseMeasure)
    (horder : ∀ᵐ xy ∂ν, Ordered xy.1 xy.2) :
    ∀ᵐ xy ∂ν, ∀ k : ℤ,
      0 < ProductCocycle.cocycleVersion θ c k xy.2 /
        ProductCocycle.cocycleVersion θ c k xy.1 ∧
      ProductCocycle.cocycleVersion θ c k xy.2 /
        ProductCocycle.cocycleVersion θ c k xy.1 ≤ 1 := by
  filter_upwards [ae_pair_all_int_finite_floor_support θ hθ0 hθ ν hfst hsnd,
    horder] with xy hs ho
  intro k
  exact ⟨div_pos (ProductCocycle.cocycleVersion_pos θ c k xy.2)
      (ProductCocycle.cocycleVersion_pos θ c k xy.1),
    ProductCocycle.cocycleVersion_ratio_le_one θ c k xy.1 xy.2 hc ho
      (hs k).1 (hs k).2⟩

theorem ae_all_selected_cocycle_ratio_cap
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (ν : Measure EndpointPair)
    (hfst : ν.map Prod.fst ≪ baseMeasure)
    (hsnd : ν.map Prod.snd ≪ baseMeasure)
    (horder : ∀ᵐ xy ∂ν, Ordered xy.1 xy.2) :
    ∀ᵐ xy ∂ν, ∀ (I : Finset ℕ) (k : ℤ),
      0 < ProductCocycle.cocycleVersion θ c k (selectedEndpoint I xy.1 xy.2) /
        ProductCocycle.cocycleVersion θ c k xy.1 ∧
      ProductCocycle.cocycleVersion θ c k (selectedEndpoint I xy.1 xy.2) /
        ProductCocycle.cocycleVersion θ c k xy.1 ≤ 1 := by
  filter_upwards [ae_pair_all_int_finite_floor_support θ hθ0 hθ ν hfst hsnd,
    horder] with xy hs ho
  intro I k
  exact ⟨div_pos (ProductCocycle.cocycleVersion_pos θ c k _)
      (ProductCocycle.cocycleVersion_pos θ c k _),
    ProductCocycle.cocycleVersion_ratio_le_one θ c k xy.1
      (selectedEndpoint I xy.1 xy.2) hc (ordered_selectedEndpoint ho I).1
      (hs k).1 (finite_floor_support_selectedEndpoint θ k xy.1 xy.2 I
        (hs k).1 (hs k).2)⟩

theorem measurableSet_all_cocycle_ratio_cap (θ c : ℕ → ℝ) :
    MeasurableSet {xy : EndpointPair | ∀ k : ℤ,
      0 < ProductCocycle.cocycleVersion θ c k xy.2 /
        ProductCocycle.cocycleVersion θ c k xy.1 ∧
      ProductCocycle.cocycleVersion θ c k xy.2 /
        ProductCocycle.cocycleVersion θ c k xy.1 ≤ 1} := by
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  have hm := ((ProductCocycle.measurable_cocycleVersion θ c k).comp measurable_snd).div
    ((ProductCocycle.measurable_cocycleVersion θ c k).comp measurable_fst)
  exact (measurableSet_lt measurable_const hm).inter
    (measurableSet_le hm measurable_const)

theorem prefixPairLaw_cocycle_ratio_cap
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (ν : Measure EndpointPair)
    (hfst : ν.map Prod.fst ≪ baseMeasure)
    (hsnd : ν.map Prod.snd ≪ baseMeasure)
    (horder : ∀ᵐ xy ∂ν, Ordered xy.1 xy.2) (D : ℕ) :
    ∀ᵐ xy ∂prefixPairLaw ν D, ∀ k : ℤ,
      0 < ProductCocycle.cocycleVersion θ c k xy.2 /
        ProductCocycle.cocycleVersion θ c k xy.1 ∧
      ProductCocycle.cocycleVersion θ c k xy.2 /
        ProductCocycle.cocycleVersion θ c k xy.1 ≤ 1 := by
  rw [prefixPairLaw, ae_map_iff (measurable_prefixPair D).aemeasurable
    (measurableSet_all_cocycle_ratio_cap θ c)]
  filter_upwards [ae_all_selected_cocycle_ratio_cap θ c hθ0 hθ hc ν hfst hsnd horder]
    with xy hxy
  exact hxy (Finset.range D)

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingAbsoluteContinuity
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.ProductModel

theorem HasUniformL2Marginals.uniformlyAbsolutelyContinuous
    {η : ℕ → Measure EndpointPair} (hη : HasUniformL2Marginals η) :
    UniformlyAbsolutelyContinuous baseMeasure (fun l => (η l).map Prod.fst) ∧
    UniformlyAbsolutelyContinuous baseMeasure (fun l => (η l).map Prod.snd) := by
  rcases hη with ⟨H, _hH, hη⟩
  constructor
  · apply EndpointLoss.uniformlyAbsolutelyContinuous_of_Lp_densities baseMeasure _ H
    intro l
    rcases hη l with ⟨f, g, hf, _hg, hmf, _hmg, hbf, _hbg⟩
    exact ⟨f, hf, hmf, hbf⟩
  · apply EndpointLoss.uniformlyAbsolutelyContinuous_of_Lp_densities baseMeasure _ H
    intro l
    rcases hη l with ⟨f, g, _hf, hg, _hmf, hmg, _hbf, hbg⟩
    exact ⟨g, hg, hmg, hbg⟩

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_PrefixCompactTransfer
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace Invariant233.ProductModel

local instance localInst_rc9804b_1 : OpensMeasurableSpace EndpointPair := inferInstance
theorem prefixPairLaw_finiteMeasure_tendsto (ν : FiniteMeasure EndpointPair) :
    Tendsto (fun D : ℕ => ν.map (prefixPair D)) atTop (𝓝 ν) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro φ
  have h := prefixPairLaw_weaklyConverges (ν : Measure EndpointPair)
    (⟨φ, φ.continuous⟩ : C(EndpointPair, ℝ))
  simpa only [prefixPairLaw, FiniteMeasure.map, FiniteMeasure.toMeasure,
    ContinuousMap.coe_mk] using h

theorem prefix_operator_relation_transfer
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (ν : FiniteMeasure EndpointPair)
    (hfst : (ν : Measure EndpointPair).map Prod.fst ≪ baseMeasure)
    (hsnd : (ν : Measure EndpointPair).map Prod.snd ≪ baseMeasure)
    (horder : ∀ᵐ xy ∂(ν : Measure EndpointPair), Ordered xy.1 xy.2)
    (hL2 : HasUniformL2Marginals (prefixPairLaw (ν : Measure EndpointPair)))
    (p : Base → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (hp : ∀ x, IsStarProjection (p x))
    (hpm : ∀ i : ℤ, Measurable (fun x => p x (lp.single 2 i 1)))
    (hzero : ∀ D, ∀ᵐ xy ∂prefixPairLaw (ν : Measure EndpointPair) D,
      (1 - p xy.2).comp
        ((_root_.OAI.Invariant233.ratioDiagonal (ProductCocycle.cocycleVersion θ c) xy).comp
          (p xy.1)) = 0) :
    ∀ᵐ xy ∂(ν : Measure EndpointPair),
      (1 - p xy.2).comp
        ((_root_.OAI.Invariant233.ratioDiagonal (ProductCocycle.cocycleVersion θ c) xy).comp
          (p xy.1)) = 0 := by
  obtain ⟨hfirst, hsecond⟩ := hL2.uniformlyAbsolutelyContinuous
  have hcapn : ∀ D k, ∀ᵐ xy ∂prefixPairLaw (ν : Measure EndpointPair) D,
      ProductCocycle.cocycleVersion θ c k xy.2 /
        ProductCocycle.cocycleVersion θ c k xy.1 ≤ 1 := by
    intro D k
    filter_upwards [prefixPairLaw_cocycle_ratio_cap θ c hθ0 hθ hc
      (ν : Measure EndpointPair) hfst hsnd horder D] with xy hxy
    exact (hxy k).2
  have hcap : ∀ k, ∀ᵐ xy ∂(ν : Measure EndpointPair),
      ProductCocycle.cocycleVersion θ c k xy.2 /
        ProductCocycle.cocycleVersion θ c k xy.1 ≤ 1 := by
    intro k
    filter_upwards [ae_ordered_cocycle_ratio_cap θ c hθ0 hθ hc
      (ν : Measure EndpointPair) hfst hsnd horder] with xy hxy
    exact (hxy k).2
  exact CompactTransfer.compact_operator_transfer baseMeasure p hp
    (ProductCocycle.cocycleVersion θ c)
    (ProductCocycle.cocycleVersion_pos θ c)
    (ProductCocycle.measurable_cocycleVersion θ c) hpm
    (prefixPairLaw_finiteMeasure_tendsto ν) hfirst hsecond
    1 zero_lt_one hcapn hcap hzero

theorem ae_of_absolutelyContinuous_finite_sum
    {α ι : Type*} [MeasurableSpace α] (s : Finset ι)
    (μ : ι → Measure α) (ν : Measure α)
    (hν : ν ≪ ∑ i ∈ s, μ i) {P : α → Prop}
    (hP : ∀ i ∈ s, ∀ᵐ x ∂μ i, P x) : ∀ᵐ x ∂ν, P x := by
  apply hν.ae_le
  rw [← Measure.sum_coe_finset]
  exact Measure.ae_sum_iff.mpr (fun i => hP i i.property)

theorem prefix_operator_relation_of_triangular_domination
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (ν : FiniteMeasure EndpointPair)
    (hfst : (ν : Measure EndpointPair).map Prod.fst ≪ baseMeasure)
    (hsnd : (ν : Measure EndpointPair).map Prod.snd ≪ baseMeasure)
    (horder : ∀ᵐ xy ∂(ν : Measure EndpointPair), Ordered xy.1 xy.2)
    (hL2 : HasUniformL2Marginals (prefixPairLaw (ν : Measure EndpointPair)))
    (hdom : ∀ D, prefixPairLaw (ν : Measure EndpointPair) D ≪
      ∑ I ∈ (Finset.range D).powerset, triangularLaw I)
    (p : Base → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (hp : ∀ x, IsStarProjection (p x))
    (hpm : ∀ i : ℤ, Measurable (fun x => p x (lp.single 2 i 1)))
    (htri : ∀ I : Finset ℕ, ∀ᵐ xy ∂triangularLaw I,
      (1 - p xy.2).comp
        ((_root_.OAI.Invariant233.ratioDiagonal (ProductCocycle.cocycleVersion θ c) xy).comp
          (p xy.1)) = 0) :
    ∀ᵐ xy ∂(ν : Measure EndpointPair),
      (1 - p xy.2).comp
        ((_root_.OAI.Invariant233.ratioDiagonal (ProductCocycle.cocycleVersion θ c) xy).comp
          (p xy.1)) = 0 := by
  apply prefix_operator_relation_transfer θ c hθ0 hθ hc ν hfst hsnd horder hL2 p hp hpm
  intro D
  exact ae_of_absolutelyContinuous_finite_sum (Finset.range D).powerset triangularLaw
    (prefixPairLaw (ν : Measure EndpointPair) D) (hdom D) (fun I _ => htri I)

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_PrefixPairIdentity
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.ProductModel

theorem prefix_pairIdentity_of_triangular_domination
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (ν : FiniteMeasure EndpointPair)
    (hfst : (ν : Measure EndpointPair).map Prod.fst ≪ baseMeasure)
    (hsnd : (ν : Measure EndpointPair).map Prod.snd ≪ baseMeasure)
    (horder : ∀ᵐ xy ∂(ν : Measure EndpointPair), Ordered xy.1 xy.2)
    (hL2 : HasUniformL2Marginals (prefixPairLaw (ν : Measure EndpointPair)))
    (hdom : ∀ D, prefixPairLaw (ν : Measure EndpointPair) D ≪
      ∑ I ∈ (Finset.range D).powerset, triangularLaw I)
    (p : Base → Fiber →L[ℂ] Fiber)
    (hp : ∀ x, IsStarProjection (p x))
    (hpm : ∀ i : ℤ, Measurable (fun x => p x (lp.single 2 i 1)))
    (htri : ∀ I : Finset ℕ, ∀ᵐ xy ∂triangularLaw I, PairIdentity θ c p xy) :
    ∀ᵐ xy ∂(ν : Measure EndpointPair), PairIdentity θ c p xy := by
  have hz := prefix_operator_relation_of_triangular_domination θ c hθ0 hθ hc ν
    hfst hsnd horder hL2 hdom p hp hpm (fun I => ?_)
  · filter_upwards [ae_ordered_cocycle_ratio_cap θ c hθ0 hθ hc
      (ν : Measure EndpointPair) hfst hsnd horder, hz] with xy hcap hzero
    refine ⟨hcap, ?_⟩
    simpa only [ratioDiagonal, cocycleRatio, Invariant233.ratioDiagonal,
      mul_assoc, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hzero
  · filter_upwards [htri I] with xy hxy
    simpa only [ratioDiagonal, cocycleRatio, Invariant233.ratioDiagonal,
      mul_assoc, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hxy.2

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductCouplingPrefix
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.flatten_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.OrderedProductCoupling

theorem prefixEndpoint_circle_endpoints (D : ℕ) (ω : Sample) :
    ProductModel.prefixEndpoint D (circleLeftEndpoint ω) (circleRightEndpoint ω) =
      circleHybridEndpoint (fun i => decide (i < D)) ω := by
  funext i
  by_cases hi : i < D <;>
    simp [ProductModel.prefixEndpoint_apply, circleLeftEndpoint,
      circleRightEndpoint, circleHybridEndpoint, circleEndpoint, hybridEndpoint, Function.comp_apply, hi]

theorem prefixPairLaw_circlePairLaw (P : Parameters) (D : ℕ) :
    ProductModel.prefixPairLaw (circlePairLaw P) D =
      (law P).map (fun ω =>
        (circleLeftEndpoint ω, circleHybridEndpoint (fun i => decide (i < D)) ω)) := by
  rw [ProductModel.prefixPairLaw, circlePairLaw,
    Measure.map_map (ProductModel.measurable_prefixPair D)
      (circleLeftEndpoint_measurable.prodMk circleRightEndpoint_measurable)]
  congr 1
  funext ω
  exact congrArg (fun y => (circleLeftEndpoint ω, y))
    (prefixEndpoint_circle_endpoints D ω)

theorem prefixPairLaw_circlePairLaw_fst (P : Parameters) (D : ℕ) :
    (ProductModel.prefixPairLaw (circlePairLaw P) D).map Prod.fst =
      (law P).map (circleHybridEndpoint (fun _ => false)) := by
  rw [ProductModel.prefixPairLaw_first_marginal]
  exact circlePairLaw_fst P

theorem prefixPairLaw_circlePairLaw_snd (P : Parameters) (D : ℕ) :
    (ProductModel.prefixPairLaw (circlePairLaw P) D).map Prod.snd =
      (law P).map (circleHybridEndpoint (fun i => decide (i < D))) := by
  rw [prefixPairLaw_circlePairLaw,
    Measure.map_map measurable_snd (circleLeftEndpoint_measurable.prodMk
      (circleHybridEndpoint_measurable (fun i => decide (i < D))))]
  rfl

theorem circlePairLaw_marginals_ac_of_energy (P : Parameters)
    (hsum : Summable (energyBound P)) :
    (circlePairLaw P).map Prod.fst ≪ ProductModel.baseMeasure ∧
      (circlePairLaw P).map Prod.snd ≪ ProductModel.baseMeasure := by
  have hhybrid (ε : ℕ → Bool) :
      (law P).map (circleHybridEndpoint ε) ≪ ProductModel.baseMeasure := by
    obtain ⟨G, _, _, _, _, hG⟩ := exists_circle_hybrid_density P ε hsum
      (le_refl (∑' i, energyBound P i))
    rw [hG]
    exact withDensity_absolutelyContinuous _ _
  constructor
  · rw [circlePairLaw_fst]
    exact hhybrid (fun _ => false)
  · rw [circlePairLaw_snd]
    exact hhybrid (fun _ => true)

theorem circlePairLaw_prefix_hasUniformL2Marginals (P : Parameters)
    (hsum : Summable (energyBound P)) :
    ProductModel.HasUniformL2Marginals
      (ProductModel.prefixPairLaw (circlePairLaw P)) := by
  let H : ℝ := Real.exp ((∑' i, energyBound P i) / 2)
  have hH : 0 ≤ H := (Real.exp_pos _).le
  have hd (ε : ℕ → Bool) :
      ∃ f : Lp ℝ 2 ProductModel.baseMeasure,
        (∀ᵐ x ∂ProductModel.baseMeasure, 0 ≤ f x) ∧
        (law P).map (circleHybridEndpoint ε) =
          ProductModel.baseMeasure.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ‖f‖ ≤ H := by
    obtain ⟨G, hG, hpos, _, hnorm, hlaw⟩ := exists_circle_hybrid_density P ε hsum
      (le_refl (∑' i, energyBound P i))
    refine ⟨hG.toLp G, ?_, ?_, ?_⟩
    · filter_upwards [hG.coeFn_toLp, hpos] with x hx hpx
      simpa only [hx, Pi.zero_apply] using hpx
    · rw [hlaw]
      apply withDensity_congr_ae
      filter_upwards [hG.coeFn_toLp] with x hx
      exact congrArg ENNReal.ofReal hx.symm
    · rw [Lp.norm_toLp]
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm).trans_eq
        (ENNReal.toReal_ofReal hH)
  refine ⟨H, hH, fun D => ?_⟩
  obtain ⟨f, hf, hflaw, hfnorm⟩ := hd (fun _ => false)
  obtain ⟨g, hg, hglaw, hgnorm⟩ := hd (fun i => decide (i < D))
  refine ⟨f, g, hf, hg, ?_, ?_, hfnorm, hgnorm⟩
  · rw [prefixPairLaw_circlePairLaw_fst]
    exact hflaw
  · rw [prefixPairLaw_circlePairLaw_snd]
    exact hglaw

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductBiasedPrefixTransfer
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.OrderedProductCoupling

theorem circlePairLaw_pairIdentity_of_triangular_domination
    (P : Parameters) (hsum : Summable (energyBound P))
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i)
    (hdom : ∀ D, ProductModel.prefixPairLaw (circlePairLaw P) D ≪
      ∑ I ∈ (Finset.range D).powerset, ProductModel.triangularLaw I)
    (p : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber)
    (hp : ∀ x, IsStarProjection (p x))
    (hpm : ∀ i : ℤ, Measurable (fun x => p x (lp.single 2 i 1)))
    (htri : ∀ I : Finset ℕ, ∀ᵐ xy ∂ProductModel.triangularLaw I,
      ProductModel.PairIdentity θ c p xy) :
    ∀ᵐ xy ∂circlePairLaw P, ProductModel.PairIdentity θ c p xy := by
  let ν : FiniteMeasure ProductModel.EndpointPair := ⟨circlePairLaw P, inferInstance⟩
  obtain ⟨hfst, hsnd⟩ := circlePairLaw_marginals_ac_of_energy P hsum
  exact ProductModel.prefix_pairIdentity_of_triangular_domination θ c hθ0 hθ hc ν
    hfst hsnd (circlePairLaw_ordered P)
    (circlePairLaw_prefix_hasUniformL2Marginals P hsum) hdom p hp hpm htri

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCoordinateSplit
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductCoordinateSplit

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

theorem measurePreserving_split
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd X p)
      (Measure.infinitePi μ)
      ((Measure.infinitePi fun i : Subtype p => μ i).prod
        (Measure.infinitePi fun i : {i // ¬ p i} => μ i)) := by
  classical
  let e := (MeasurableEquiv.piEquivPiSubtypeProd X p).symm
  apply MeasurePreserving.symm e
  refine ⟨e.measurable, ?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  have heq : e ⁻¹' Set.pi (s : Set ι) t =
      (Set.pi (s.subtype p) (fun i : Subtype p => t i)) ×ˢ
      (Set.pi (s.subtype (fun i => ¬ p i)) (fun i : {i // ¬p i} => t i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod,
      Finset.mem_subtype]
    constructor
    · intro h
      constructor
      · intro i hi
        have := h i hi
        simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, i.property]
          using this
      · intro i hi
        have := h i hi
        simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, i.property]
          using this
    · rintro ⟨hpos, hneg⟩ i hi
      by_cases hip : p i
      · simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hip]
          using hpos ⟨i, hip⟩ hi
      · simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hip]
          using hneg ⟨i, hip⟩ hi
  rw [e.map_apply, heq, Measure.prod_prod,
    Measure.infinitePi_pi (fun i : Subtype p => μ i) (fun i _ => ht i),
    Measure.infinitePi_pi (fun i : {i // ¬p i} => μ i) (fun i _ => ht i)]
  rw [Finset.prod_subtype_eq_prod_filter (s := s) (p := p) (fun i => μ i (t i)),
    Finset.prod_subtype_eq_prod_filter (s := s) (p := fun i => ¬p i) (fun i => μ i (t i)),
    Finset.prod_filter_mul_prod_filter_not]

end Invariant233.ProductCoordinateSplit

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_FiniteProductAbsoluteContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233

theorem fin_pi_absolutelyContinuous {n : ℕ} {X : Fin n → Type*}
    [∀ i, MeasurableSpace (X i)] (μ ν : (i : Fin n) → Measure (X i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (h : ∀ i, μ i ≪ ν i) : Measure.pi μ ≪ Measure.pi ν := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
  | succ n ih =>
    have ht : Measure.pi (fun i : Fin n => μ (Fin.succAbove 0 i)) ≪
        Measure.pi (fun i : Fin n => ν (Fin.succAbove 0 i)) :=
      ih (fun i => μ (Fin.succAbove 0 i)) (fun i => ν (Fin.succAbove 0 i))
        (fun i => h (Fin.succAbove 0 i))
    have hp := (h 0).prod ht
    have hm := (measurePreserving_piFinSuccAbove μ 0).symm
    have hn := (measurePreserving_piFinSuccAbove ν 0).symm
    have hx := hp.map (MeasurableEquiv.piFinSuccAbove X 0).symm.measurable
    rwa [hm.map_eq, hn.map_eq] at hx

theorem fintype_pi_absolutelyContinuous {I : Type*} [Fintype I]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ ν : (i : I) → Measure (X i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (h : ∀ i, μ i ≪ ν i) : Measure.pi μ ≪ Measure.pi ν := by
  let e := (Fintype.equivFin I).symm
  have ha := fin_pi_absolutelyContinuous (fun i => μ (e i)) (fun i => ν (e i))
    (fun i => h (e i))
  have hmap := ha.map (MeasurableEquiv.piCongrLeft X e).measurable
  rwa [(measurePreserving_piCongrLeft μ e).map_eq,
    (measurePreserving_piCongrLeft ν e).map_eq] at hmap

theorem pi_finite_sum {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : (i : I) → J → Measure (X i)) [∀ i j, IsFiniteMeasure (μ i j)] :
    Measure.pi (fun i => ∑ j, μ i j) =
      ∑ pattern : I → J, Measure.pi (fun i => μ i (pattern i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  simp_rw [Measure.finsetSum_apply, Measure.pi_pi]
  exact (Fintype.prod_sum (fun i j => μ i j (s i))).symm

theorem pi_add_eq_sum_bool {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ ν : (i : I) → Measure (X i))
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)] :
    Measure.pi (fun i => μ i + ν i) =
      ∑ pattern : I → Bool, Measure.pi (fun i => if pattern i then ν i else μ i) := by
  have : ∀ i (b : Bool), IsFiniteMeasure (if b then ν i else μ i) := by
    intro i b
    cases b <;> simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true] <;> infer_instance
  simpa only [Fintype.sum_bool, Bool.false_eq_true, ite_false, if_false, ite_true, if_true, add_comm] using
    pi_finite_sum (fun i (b : Bool) => if b then ν i else μ i)

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_PrefixDomination
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.CouplingMixture

lemma intervalLaw_pair_strictly_ordered {a b c d : ℝ} (hbc : b ≤ c) :
    ∀ᵐ z ∂(intervalLaw a b).prod (intervalLaw c d), z.1 < z.2 := by
  have : IsZeroOrProbabilityMeasure (intervalLaw a b) := inferInstanceAs
    (IsZeroOrProbabilityMeasure (volume[|Ico a b]))
  have : IsZeroOrProbabilityMeasure (intervalLaw c d) := inferInstanceAs
    (IsZeroOrProbabilityMeasure (volume[|Ico c d]))
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_fst measurable_snd)]
  filter_upwards [intervalLaw_ae_mem a b] with x hx
  filter_upwards [intervalLaw_ae_mem c d] with y hy
  exact hx.2.trans_le (hbc.trans hy.1)

end Invariant233.CouplingMixture

namespace Invariant233.OneCoordinateCoupling

open CouplingMixture

lemma replacement_ae_strictly_ordered {m a b : ℝ} (hm : 2 ≤ m) (i : Fin 5) :
    ∀ᵐ z ∂(leftLaw m a b i).prod (rightLaw m a b i), z.1 < z.2 := by
  have hm0 : 0 < m := by linarith
  have hinv : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [leftLaw, rightLaw]
  all_goals apply intervalLaw_pair_strictly_ordered
  all_goals linarith

lemma replacement_eq_triangle_withDensity {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    (leftLaw m a b i).prod (rightLaw m a b i) =
      triangleLaw.withDensity (replacementDensity m a b i) := by
  have hl : Measurable (fun x => ENNReal.ofReal (leftDensity m a b i x)) := by
    apply Measurable.ennreal_ofReal
    fin_cases i <;> exact intervalDensity_measurable _ _
  have hr : Measurable (fun x => ENNReal.ofReal (rightDensity m a b i x)) := by
    apply Measurable.ennreal_ofReal
    fin_cases i <;> exact intervalDensity_measurable _ _
  have hd : (leftLaw m a b i).prod (rightLaw m a b i) =
      (baseLaw.prod baseLaw).withDensity (replacementDensity m a b i) := by
    rw [leftLaw_eq_withDensity hm ha0 ha1 hb0 hb1,
      rightLaw_eq_withDensity hm ha0 ha1 hb0 hb1, prod_withDensity hl hr]
    rfl
  have hs : ((leftLaw m a b i).prod (rightLaw m a b i)).restrict
      {z : ℝ × ℝ | z.1 < z.2} = (leftLaw m a b i).prod (rightLaw m a b i) :=
    Measure.restrict_eq_self_of_ae_mem
      (replacement_ae_strictly_ordered (a := a) (b := b) hm i)
  rw [hd, restrict_withDensity (measurableSet_lt measurable_fst measurable_snd)] at hs
  exact hd.trans hs.symm

lemma replacement_absolutelyContinuous_triangle {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    (leftLaw m a b i).prod (rightLaw m a b i) ≪ triangleLaw := by
  rw [replacement_eq_triangle_withDensity hm ha0 ha1 hb0 hb1]
  exact withDensity_absolutelyContinuous _ _

lemma pairLaw_absolutelyContinuous_diagonal_add_triangle {κ m a b t : ℝ}
    (hm : 2 ≤ m) (ha0 : 0 < a) (ha1 : a ≤ 1 / 4)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) :
    pairLaw κ m a b t ≪ diagonal baseLaw + triangleLaw := by
  unfold pairLaw mixture
  apply Measure.AbsolutelyContinuous.add_left
  · exact (Measure.AbsolutelyContinuous.rfl.add_right triangleLaw).smul_left _
  · rw [← Measure.sum_fintype]
    apply Measure.absolutelyContinuous_sum_left
    intro i
    exact ((replacement_absolutelyContinuous_triangle hm ha0 ha1 hb0 hb1 i).add_right'
      (diagonal baseLaw)).smul_left _

end Invariant233.OneCoordinateCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductPrefixDomination
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.flatten_unflatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.OrderedProductCoupling

open OneCoordinateCoupling CouplingMixture

lemma assemblePrefixPair_measurable (D : ℕ) : Measurable (assemblePrefixPair D) := by
  apply Measurable.prodMk
  all_goals
    apply Measurable.of_eval
    intro i
    by_cases hi : i ∈ Finset.range D
    · simp only [dite_eq_left hi]
      fun_prop
    · simp only [dite_eq_right hi]
      fun_prop

lemma prefixPairsLaw_absolutelyContinuous (P : Parameters) (D : ℕ) :
    prefixPairsLaw P D ≪ prefixReferenceLaw D := by
  unfold prefixPairsLaw prefixReferenceLaw
  rw [← Invariant233.pi_add_eq_sum_bool
    (fun _ : PrefixIndex D => diagonal baseLaw) (fun _ => triangleLaw)]
  apply Invariant233.fintype_pi_absolutelyContinuous
  intro i
  have hm0 : 0 < P.m i := by linarith [P.m_ge i]
  exact pairLaw_absolutelyContinuous_diagonal_add_triangle
    (by linarith [P.m_ge i])
    (CouplingMarginalBounds.width_pos hm0 (P.a_lower i)) (P.a_upper i)
    (CouplingMarginalBounds.width_pos hm0 (P.b_lower i)) (P.b_upper i)

lemma prefix_payload_map (P : Parameters) (D : ℕ) :
    (law P).map (fun ω =>
      ((fun i : PrefixIndex D => (ω i).2), (fun i : TailIndex D => (ω i).2.1))) =
      (prefixPairsLaw P D).prod (leftTailLaw P D) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ℕ => CoordinateSample)
    (fun i => i ∈ Finset.range D)
  let f : (PrefixIndex D → CoordinateSample) → PrefixPairs D := fun ω i => (ω i).2
  let g : (TailIndex D → CoordinateSample) → TailValues D := fun ω i => (ω i).2.1
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  have he := ProductCoordinateSplit.measurePreserving_split (coordinateLaw P)
    (fun i => i ∈ Finset.range D)
  have : ∀ i : PrefixIndex D, IsProbabilityMeasure ((coordinateLaw P i).map Prod.snd) :=
    fun _ => inferInstance
  have hp : (Measure.infinitePi (fun i : PrefixIndex D => coordinateLaw P i)).map f =
      prefixPairsLaw P D := by
    rw [Measure.infinitePi_map_pi _ (fun _ => measurable_snd), Measure.infinitePi_eq_pi]
    simp only [coordinateLaw_map_pair]
    rfl
  have ht : (Measure.infinitePi (fun i : TailIndex D => coordinateLaw P i)).map g =
      leftTailLaw P D :=
    Measure.infinitePi_map_pi _ (fun _ => measurable_snd.fst)
  change (law P).map ((Prod.map f g) ∘ e) = _
  have heq : (law P).map e =
      (Measure.infinitePi (fun i : PrefixIndex D => coordinateLaw P i)).prod
        (Measure.infinitePi (fun i : TailIndex D => coordinateLaw P i)) := he.map_eq
  rw [← Measure.map_map (hf.prodMap hg) e.measurable, heq]
  rw [← Measure.map_prod_map _ _ hf hg, hp, ht]

lemma prefixPairLaw_factorization (P : Parameters) (D : ℕ) :
    prefixPairLaw P D =
      ((prefixPairsLaw P D).prod (leftTailLaw P D)).map (assemblePrefixPair D) := by
  rw [← prefix_payload_map]
  rw [Measure.map_map (assemblePrefixPair_measurable D) (by fun_prop)]
  unfold prefixPairLaw
  congr 1
  funext ω
  apply Prod.ext <;> funext i
  all_goals
    by_cases hi : i ∈ Finset.range D
    · simp_all [assemblePrefixPair, hybridEndpoint, leftEndpoint, rightEndpoint, Finset.mem_range]
    · simp_all [assemblePrefixPair, hybridEndpoint, leftEndpoint, rightEndpoint, Finset.mem_range]

lemma leftEndpoint_map_infinitePi (P : Parameters) :
    (law P).map leftEndpoint = Measure.infinitePi
      (fun i => (coordinateLaw P i).map (fun z => z.2.1)) :=
  Measure.infinitePi_map_pi _ (fun _ => measurable_snd.fst)

lemma leftTailLaw_absolutelyContinuous (P : Parameters)
    (hsum : Summable (energyBound P)) (D : ℕ) : leftTailLaw P D ≪ baseTailLaw D := by
  obtain ⟨H, _, _, _, _, hH⟩ := exists_hybrid_density P (fun _ => false)
    hsum (le_refl (∑' i, energyBound P i))
  have hleft : (law P).map leftEndpoint =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) := by
    have heq : hybridEndpoint (fun _ => false) = leftEndpoint := by
      funext ω i
      rfl
    rw [heq] at hH
    exact hH
  have hac : (law P).map leftEndpoint ≪ baseMeasure := by
    rw [hleft]
    exact withDensity_absolutelyContinuous _ _
  have hmap := hac.map (show Measurable (fun x (i : TailIndex D) => x i) from by fun_prop)
  rw [leftEndpoint_map_infinitePi] at hmap
  have : ∀ i, IsProbabilityMeasure ((coordinateLaw P i).map (fun z => z.2.1)) :=
    fun _ => Measure.isProbabilityMeasure_map
      (show Measurable (fun z : CoordinateSample => z.2.1) by fun_prop).aemeasurable
  have htail : (Measure.infinitePi
      (fun i => (coordinateLaw P i).map (fun z => z.2.1))).map
      (fun x (i : TailIndex D) => x i) = leftTailLaw P D :=
    Measure.infinitePi_map_restrict' _
  have hbase : baseMeasure.map (fun x (i : TailIndex D) => x i) = baseTailLaw D :=
    Measure.infinitePi_map_restrict' _
  rwa [htail, hbase] at hmap

lemma prefixPairLaw_absolutelyContinuous (P : Parameters)
    (hsum : Summable (energyBound P)) (D : ℕ) :
    prefixPairLaw P D ≪ prefixReferencePairLaw D := by
  rw [prefixPairLaw_factorization]
  exact ((prefixPairsLaw_absolutelyContinuous P D).prod
    (leftTailLaw_absolutelyContinuous P hsum D)).map (assemblePrefixPair_measurable D)

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_PrefixReferenceIdentification
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.OrderedProductCoupling

lemma referencePayload_measurable (D : ℕ) :
    Measurable (referencePayload D) := by
  unfold referencePayload
  fun_prop

theorem referencePayload_map (D : ℕ) :
    (baseMeasure.prod baseMeasure).map (referencePayload D) =
      (Measure.pi (fun _ : PrefixIndex D =>
        OneCoordinateCoupling.baseLaw.prod OneCoordinateCoupling.baseLaw)).prod
          (baseTailLaw D) := by
  let A := PrefixIndex D → ℝ
  let μ : Measure A := Measure.pi (fun _ => OneCoordinateCoupling.baseLaw)
  let ν := baseTailLaw D
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ℕ => ℝ)
    (fun i => i ∈ Finset.range D)
  have hs : MeasurePreserving e baseMeasure (μ.prod ν) := by
    simpa only [e, μ, ν, A, baseMeasure, baseTailLaw, Measure.infinitePi_eq_pi] using
      ProductCoordinateSplit.measurePreserving_split
        (fun _ : ℕ => OneCoordinateCoupling.baseLaw) (fun i => i ∈ Finset.range D)
  have hr : MeasurePreserving (Finset.range D).restrict baseMeasure μ :=
    ⟨Finset.measurable_restrict _, Measure.infinitePi_map_restrict _⟩
  have ha := measurePreserving_prodAssoc μ ν μ
  have hb := (MeasurePreserving.id μ).prod
    (Measure.measurePreserving_swap (μ := ν) (ν := μ))
  have hc := (measurePreserving_prodAssoc μ μ ν).symm
  have hd := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (PrefixIndex D)
    (fun _ => OneCoordinateCoupling.baseLaw)
    (fun _ => OneCoordinateCoupling.baseLaw)).symm
  have h := ((hd.prod (MeasurePreserving.id ν)).comp
    (hc.comp (hb.comp (ha.comp (hs.prod hr))))).map_eq
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1

theorem referencePayload_restrict (D : ℕ) (s : Set (PrefixPairs D))
    (hs : MeasurableSet s) :
    ((baseMeasure.prod baseMeasure).restrict
      (referencePayload D ⁻¹' (s ×ˢ Set.univ))).map (referencePayload D) =
      ((Measure.pi (fun _ : PrefixIndex D =>
        OneCoordinateCoupling.baseLaw.prod OneCoordinateCoupling.baseLaw)).restrict s).prod
        (baseTailLaw D) := by
  rw [← Measure.restrict_map (referencePayload_measurable D) (hs.prod .univ),
    referencePayload_map, ← Measure.restrict_prod_eq_prod_univ]

theorem uniform_pair_map_diagonal :
    (OneCoordinateCoupling.baseLaw.prod OneCoordinateCoupling.baseLaw).map
      (fun z : ℝ × ℝ => (z.1, z.1)) =
        CouplingMixture.diagonal OneCoordinateCoupling.baseLaw := by
  have hf : Measurable (fun x : ℝ => (x, x)) := measurable_id.prodMk measurable_id
  rw [show (fun z : ℝ × ℝ => (z.1, z.1)) = (fun x : ℝ => (x, x)) ∘ Prod.fst from rfl,
    ← Measure.map_map hf measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  rfl

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductPrefixCircle
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.flatten_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.OrderedProductCoupling

lemma circleHybridEndpoint_selected (I : Finset ℕ) (ω : Sample) :
    circleHybridEndpoint (fun i => decide (i ∈ I)) ω =
      ProductModel.selectedEndpoint I (circleLeftEndpoint ω) (circleRightEndpoint ω) := by
  funext i
  by_cases hi : i ∈ I <;>
    simp [circleHybridEndpoint, circleLeftEndpoint, circleRightEndpoint,
      circleEndpoint, hybridEndpoint, ProductModel.selectedEndpoint, hi]

theorem map_prefixPairLaw_circle (P : Parameters) (D : ℕ) :
    (prefixPairLaw P D).map circlePairEndpoint =
      ProductModel.prefixPairLaw (circlePairLaw P) D := by
  rw [prefixPairLaw, Measure.map_map circlePairEndpoint_measurable
    (leftEndpoint_measurable.prodMk (hybridEndpoint_measurable _)),
    ProductModel.prefixPairLaw, circlePairLaw,
    Measure.map_map (ProductModel.measurable_prefixPair D)
      (circleLeftEndpoint_measurable.prodMk circleRightEndpoint_measurable)]
  congr 1
  funext ω
  exact Prod.ext rfl (circleHybridEndpoint_selected (Finset.range D) ω)

theorem map_sum_realTriangularLaw (s : Finset (Finset ℕ)) :
    (∑ I ∈ s, realTriangularLaw I).map circlePairEndpoint =
      ∑ I ∈ s, ProductModel.triangularLaw I := by
  rw [CouplingMixture.map_finsetSum s _ circlePairEndpoint_measurable]
  simp_rw [map_realTriangularLaw]

theorem map_absolutelyContinuous_sum_triangularLaw (s : Finset (Finset ℕ))
    {ν : Measure (Endpoint × Endpoint)} (hν : ν ≪ ∑ I ∈ s, realTriangularLaw I) :
    ν.map circlePairEndpoint ≪ ∑ I ∈ s, ProductModel.triangularLaw I := by
  simpa only [map_sum_realTriangularLaw] using hν.map circlePairEndpoint_measurable

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_PrefixReferenceCompletion
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.OrderedProductCoupling
open OneCoordinateCoupling CouplingMixture

lemma collapsePrefixPattern_measurable (D : ℕ) (pattern : PrefixIndex D → Bool) :
    Measurable (collapsePrefixPattern D pattern) := by
  apply Measurable.of_eval
  intro i
  cases hp : pattern i <;> simp only [collapsePrefixPattern, hp, Bool.false_eq_true,
    ite_false, if_false, ite_true, if_true] <;> fun_prop

lemma prefixPatternEvent_measurable (D : ℕ) (pattern : PrefixIndex D → Bool) :
    MeasurableSet (prefixPatternEvent D pattern) := by
  simp only [prefixPatternEvent, ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_lt ((measurable_pi_apply i).fst) ((measurable_pi_apply i).snd)

lemma prefixPattern_restrict_map (D : ℕ) (pattern : PrefixIndex D → Bool) :
    ((Measure.pi (fun _ : PrefixIndex D => baseLaw.prod baseLaw)).restrict
      (prefixPatternEvent D pattern)).map (collapsePrefixPattern D pattern) =
      Measure.pi (fun i => if pattern i then triangleLaw else diagonal baseLaw) := by
  let A : PrefixIndex D → Set (ℝ × ℝ) :=
    fun i => if pattern i then {z | z.1 < z.2} else Set.univ
  have hA : prefixPatternEvent D pattern = Set.univ.pi A := by
    ext z
    simp only [prefixPatternEvent, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
      forall_const]
    apply forall_congr'
    intro i
    cases hp : pattern i <;> simp [A, hp]
  rw [hA, Measure.restrict_pi_pi]
  have hm (i : PrefixIndex D) :
      Measurable (fun z : ℝ × ℝ => if pattern i then z else (z.1,z.1)) := by
    cases hp : pattern i <;> simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true] <;>
      fun_prop
  have hi (i : PrefixIndex D) :
      ((baseLaw.prod baseLaw).restrict (A i)).map
        (fun z : ℝ × ℝ => if pattern i then z else (z.1,z.1)) =
        if pattern i then triangleLaw else diagonal baseLaw := by
    cases hp : pattern i
    · simpa [A, hp] using uniform_pair_map_diagonal
    · simp [A, hp, triangleLaw]
  have (i : PrefixIndex D) : IsFiniteMeasure ((baseLaw.prod baseLaw).restrict (A i)) :=
    (by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply collapsePrefixPattern_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  have (i : PrefixIndex D) : IsFiniteMeasure
      (((baseLaw.prod baseLaw).restrict (A i)).map
        (fun z : ℝ × ℝ => if pattern i then z else (z.1,z.1))) := inferInstance
  change (Measure.pi (fun i => (baseLaw.prod baseLaw).restrict (A i))).map
    (fun z i => if pattern i then z i else ((z i).1,(z i).1)) = _
  rw [Measure.pi_map_pi (fun i => (hm i).aemeasurable)]
  simp_rw [hi]

lemma mem_selectedPrefixPattern (D : ℕ) (pattern : PrefixIndex D → Bool) (i : ℕ) :
    i ∈ selectedPrefixPattern D pattern ↔
      ∃ hi : i ∈ Finset.range D, pattern ⟨i, hi⟩ = true := by
  classical
  simp only [selectedPrefixPattern, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, hji⟩
    subst i
    exact ⟨j.property, hj⟩
  · rintro ⟨hi, hp⟩
    exact ⟨⟨i, hi⟩, hp, rfl⟩

lemma selectedPrefixPattern_subset (D : ℕ) (pattern : PrefixIndex D → Bool) :
    selectedPrefixPattern D pattern ⊆ Finset.range D := by
  intro i hi
  exact ((mem_selectedPrefixPattern D pattern i).1 hi).choose

lemma mem_selectedPrefixPattern_subtype (D : ℕ) (pattern : PrefixIndex D → Bool)
    (i : PrefixIndex D) : i.val ∈ selectedPrefixPattern D pattern ↔ pattern i = true := by
  rw [mem_selectedPrefixPattern]
  exact ⟨fun ⟨_, hp⟩ => hp, fun hp => ⟨i.property, hp⟩⟩

lemma realTriangularEvent_eq_payload_preimage (D : ℕ) (pattern : PrefixIndex D → Bool) :
    realTriangularEvent (selectedPrefixPattern D pattern) =
      referencePayload D ⁻¹' (prefixPatternEvent D pattern ×ˢ Set.univ) := by
  ext xz
  change (∀ i ∈ selectedPrefixPattern D pattern, xz.1 i < xz.2 i) ↔ _
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true,
    prefixPatternEvent, Set.mem_ofPred_eq, referencePayload]
  constructor
  · intro h i hi
    exact h i ((mem_selectedPrefixPattern_subtype D pattern i).2 hi)
  · intro h i hi
    obtain ⟨hiD, hip⟩ := (mem_selectedPrefixPattern D pattern i).1 hi
    exact h ⟨i, hiD⟩ hip

lemma assemble_collapse_referencePayload (D : ℕ) (pattern : PrefixIndex D → Bool)
    (xz : Endpoint × Endpoint) :
    assemblePrefixPair D
      (collapsePrefixPattern D pattern (referencePayload D xz).1,
        (referencePayload D xz).2) =
      (xz.1, realSelectedEndpoint (selectedPrefixPattern D pattern) xz.1 xz.2) := by
  apply Prod.ext <;> funext i
  · by_cases hi : i ∈ Finset.range D
    · cases hp : pattern ⟨i, hi⟩ <;>
        simp only [assemblePrefixPair, dite_eq_left hi, collapsePrefixPattern, referencePayload, hp, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
    · simp only [assemblePrefixPair, dite_eq_right hi, referencePayload]
  · by_cases hi : i ∈ Finset.range D
    · have hmem := mem_selectedPrefixPattern_subtype D pattern ⟨i, hi⟩
      cases hp : pattern ⟨i, hi⟩ <;>
        simp only [assemblePrefixPair, dite_eq_left hi, collapsePrefixPattern, referencePayload, hp, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
      all_goals simp_all only [realSelectedEndpoint, Bool.false_eq_true, not_false_eq_true, ite_eq_left, ite_eq_right]
    · have hn : i ∉ selectedPrefixPattern D pattern :=
        fun h => hi (selectedPrefixPattern_subset D pattern h)
      simp only [assemblePrefixPair, dite_eq_right hi, referencePayload, realSelectedEndpoint, ite_eq_right hn]

theorem prefixPatternLaw_eq_realTriangularLaw (D : ℕ) (pattern : PrefixIndex D → Bool) :
    ((Measure.pi (fun i : PrefixIndex D =>
      if pattern i then triangleLaw else CouplingMixture.diagonal baseLaw)).prod
        (baseTailLaw D)).map (assemblePrefixPair D) =
      realTriangularLaw (selectedPrefixPattern D pattern) := by
  have : IsFiniteMeasure (Measure.pi (fun _ : PrefixIndex D => baseLaw.prod baseLaw)) :=
    (by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply assemblePrefixPair_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  have : IsFiniteMeasure ((Measure.pi (fun _ : PrefixIndex D => baseLaw.prod baseLaw)).restrict
      (prefixPatternEvent D pattern)) := inferInstance
  have : SigmaFinite ((Measure.pi (fun _ : PrefixIndex D => baseLaw.prod baseLaw)).restrict
      (prefixPatternEvent D pattern)) := IsFiniteMeasure.toSigmaFinite _
  let R : PrefixPairs D × TailValues D → PrefixPairs D × TailValues D :=
    Prod.map (collapsePrefixPattern D pattern) id
  have hR : Measurable R := (collapsePrefixPattern_measurable D pattern).prodMap measurable_id
  have hfun : (fun xz : Endpoint × Endpoint =>
      (xz.1, realSelectedEndpoint (selectedPrefixPattern D pattern) xz.1 xz.2)) =
      (assemblePrefixPair D ∘ R) ∘ referencePayload D := by
    funext xz
    exact (assemble_collapse_referencePayload D pattern xz).symm
  symm
  rw [realTriangularLaw, hfun, realTriangularEvent_eq_payload_preimage,
    ← Measure.map_map ((assemblePrefixPair_measurable D).comp hR)
      (referencePayload_measurable D),
    referencePayload_restrict D _ (prefixPatternEvent_measurable D pattern),
    ← Measure.map_map (assemblePrefixPair_measurable D) hR]
  change (((((Measure.pi (fun _ : PrefixIndex D => baseLaw.prod baseLaw)).restrict
      (prefixPatternEvent D pattern)).prod (baseTailLaw D)).map
        (Prod.map (collapsePrefixPattern D pattern) id)).map (assemblePrefixPair D)) = _
  rw [← Measure.map_prod_map
      ((Measure.pi (fun _ : PrefixIndex D => baseLaw.prod baseLaw)).restrict
        (prefixPatternEvent D pattern)) (baseTailLaw D)
      (collapsePrefixPattern_measurable D pattern) measurable_id,
    Measure.map_id, prefixPattern_restrict_map]

theorem prefixReferencePairLaw_absolutelyContinuous (D : ℕ) :
    prefixReferencePairLaw D ≪
      ∑ I ∈ (Finset.range D).powerset, realTriangularLaw I := by
  classical
  unfold prefixReferencePairLaw prefixReferenceLaw
  rw [← Measure.sum_fintype, Measure.prod_sum_left,
    Measure.map_sum (assemblePrefixPair_measurable D).aemeasurable]
  apply Measure.absolutelyContinuous_sum_left
  intro pattern
  rw [prefixPatternLaw_eq_realTriangularLaw]
  apply Measure.absolutelyContinuous_of_le
  exact Finset.single_le_sum (fun I _ => bot_le)
    (Finset.mem_powerset.mpr (selectedPrefixPattern_subset D pattern))

theorem circle_prefix_absolutelyContinuous_triangular_sum (P : Parameters)
    (hsum : Summable (energyBound P)) (D : ℕ) :
    ProductModel.prefixPairLaw (circlePairLaw P) D ≪
      ∑ I ∈ (Finset.range D).powerset, ProductModel.triangularLaw I := by
  have h := map_absolutelyContinuous_sum_triangularLaw (Finset.range D).powerset
    ((prefixPairLaw_absolutelyContinuous P hsum D).trans
      (prefixReferencePairLaw_absolutelyContinuous D))
  simpa only [map_prefixPairLaw_circle] using h

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductBiasedIdentityFromTriangular
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.OrderedProductCoupling

theorem circlePairLaw_pairIdentity_of_triangular
    (P : Parameters) (hsum : Summable (energyBound P))
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i)
    (F : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber)
    (hF : ∀ x, IsStarProjection (F x))
    (hFm : ∀ i : ℤ, Measurable (fun x => F x (lp.single 2 i 1)))
    (htri : ∀ I : Finset ℕ, ∀ᵐ xy ∂ProductModel.triangularLaw I,
      ProductModel.PairIdentity θ c F xy) :
    ∀ᵐ xy ∂circlePairLaw P, ProductModel.PairIdentity θ c F xy :=
  circlePairLaw_pairIdentity_of_triangular_domination P hsum θ c hθ0 hθ hc
    (circle_prefix_absolutelyContinuous_triangular_sum P hsum) F hF hFm htri

theorem source_circlePairLaw_pairIdentity_of_triangular_oai
    (m : ℕ → ℕ) (a b : ℕ → ℝ) (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s))
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i)
    (F : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber)
    (hF : ∀ x, IsStarProjection (F x))
    (hFm : ∀ i : ℤ, Measurable (fun x => F x (lp.single 2 i 1)))
    (htri : ∀ I : Finset ℕ, ∀ᵐ xy ∂ProductModel.triangularLaw I,
      ProductModel.PairIdentity θ c F xy) :
    ∀ tag : ℕ, ∀ᵐ xy ∂circlePairLaw
      (ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm ha ha' hb hb' e tag),
      ProductModel.PairIdentity θ c F xy := by
  intro tag
  exact circlePairLaw_pairIdentity_of_triangular _
    (ofBlocks_energy_sum m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm
      ha ha' hb hb' e tag summable_sourceKappa_sq).1 θ c hθ0 hθ hc F hF hFm htri

end Invariant233.OrderedProductCoupling

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.OrderedProductCoupling.source_circlePairLaw_pairIdentity_of_triangular_oai := @OAI.Invariant233.OrderedProductCoupling.source_circlePairLaw_pairIdentity_of_triangular_oai
