-- Prove2me | solution 1 for MarkovProcess.brownianMotion_map_finsetEvaluation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:44:16.086325+00:00
-- url     : https://prove2.me/submissions/69423f1e-b024-4feb-9bfe-4b3405af09b8

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_DenseTime_TwoPointMarginals_b3a3d14b
import Definitions.Def_MarkovProcess_V3H_Feller_BackwardC0Integral_1512e54f
import Definitions.Def_MarkovProcess_V3H_Feller_DensePhysicalFiniteSetContinuity_75f8b26c
import Definitions.Def_MarkovProcess_V3H_FiniteTime_CoordinateProductActiveReduction_0fcd6a29
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelCompactTestTransport_3904fd05
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelShift_14b03019
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelRestriction_041bf9e5
import Definitions.Def_MarkovProcess_V3H_Kernel_FiniteRestrictionIdentification_619c5320
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_Polish_87f91693
import Definitions.Def_MarkovProcess_V3H_Path_RandomShiftMeasurability_fbe17c52
import Definitions.Def_MarkovProcess_V3H_Path_ShiftCompactTestConvergence_fc2b2de1
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Definitions.Def_MarkovProcess_V3H_Path_StoppingTimeDyadicCeiling_2d75c809
import Definitions.Def_MarkovProcess_V3H_Time_FiniteDenseApproximationOrdered_4fc0c4f5
import Definitions.Def_MarkovProcess_V3H_Trajectory_DenseRestrictionMarginals_931e4c17
import Definitions.Def_MarkovProcess_V3H_Trajectory_FellerRestrictedRestart_8026f3b2
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelEquivariance_10113825
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Trajectory_Equivariance_2a745e86
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_MarkovProcess_V3H_Examples_HeatSemigroup_43feba3c
import Definitions.Def_MarkovProcess_V3H_Feller_Resolvent_4f8c89b8
import Definitions.Def_MarkovProcess_V3H_Trajectory_Dynkin_eb6ae7c0
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The one-dimensional heat semigroup and its continuous-path process

The transition semigroup on the real line whose kernel at time `t` is the Gaussian law with mean
the starting point and variance `t`.  It is conservative, Feller, and satisfies the Kolmogorov
moment criterion with exponents `p = 4`, `q = 2` and the fourth moment of the standard Gaussian as
constant, so the existence-and-uniqueness theorem of `MarkovProcess.Main` applies to it.  The
process it produces is named `brownianMotion`.

Main results:

* `heatSemigroup`, `heatSemigroup_apply`: the semigroup and its Gaussian transition measures.
* `isConservative_heatSemigroup`: no mass is lost.
* `kernelIntegral_heatSemigroup`: the scaling representation of the transition operator.
* `isFellerKernelSemigroup_heatSemigroup`: the Feller property.
* `heatResolvent`: its positive contractive `C₀` resolvent.
* `heatExhaustion`: the explicit exhaustion `x ↦ 1 / (1 + |x|)`.
* `hasKolmogorovMoments_heatSemigroup`: the intrinsic Kolmogorov moment bound.
* `existsUnique_continuousProcess_heatSemigroup`: the main theorem, applied.
* `brownianMotion`, `brownianMotion_map_eval`, `brownianMotion_map_finsetEvaluation`: the
  continuous-path process and its finite-dimensional distributions.

Only one space dimension is treated: the multidimensional heat semigroup is not constructed here.
Nothing in this file asserts independence of increments; that is proved in
`MarkovProcess.Examples.BrownianMotion`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

noncomputable section

section Gaussian





end Gaussian

section Definition





















end Definition

section Feller





















end Feller

section OnePointExhaustion













end OnePointExhaustion

section Moments











end Moments

section Process















end Process

end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The one-dimensional heat semigroup and its continuous-path process

The transition semigroup on the real line whose kernel at time `t` is the Gaussian law with mean
the starting point and variance `t`.  It is conservative, Feller, and satisfies the Kolmogorov
moment criterion with exponents `p = 4`, `q = 2` and the fourth moment of the standard Gaussian as
constant, so the existence-and-uniqueness theorem of `MarkovProcess.Main` applies to it.  The
process it produces is named `brownianMotion`.

Main results:

* `heatSemigroup`, `heatSemigroup_apply`: the semigroup and its Gaussian transition measures.
* `isConservative_heatSemigroup`: no mass is lost.
* `kernelIntegral_heatSemigroup`: the scaling representation of the transition operator.
* `isFellerKernelSemigroup_heatSemigroup`: the Feller property.
* `heatResolvent`: its positive contractive `C₀` resolvent.
* `heatExhaustion`: the explicit exhaustion `x ↦ 1 / (1 + |x|)`.
* `hasKolmogorovMoments_heatSemigroup`: the intrinsic Kolmogorov moment bound.
* `existsUnique_continuousProcess_heatSemigroup`: the main theorem, applied.
* `brownianMotion`, `brownianMotion_map_eval`, `brownianMotion_map_finsetEvaluation`: the
  continuous-path process and its finite-dimensional distributions.

Only one space dimension is treated: the multidimensional heat semigroup is not constructed here.
Nothing in this file asserts independence of increments; that is proved in
`MarkovProcess.Examples.BrownianMotion`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal ZeroAtInfty





















section AuxSec
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]
variable (P : MarkovProcess.SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative

open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup

omit [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha] [LocallyCompactSpace alpha] in
theorem AuxB_reindex {n m : ℕ} (h : m = n) (times : FiniteOrderedTimes n)
    (t' : FiniteOrderedTimes m) (ht : ∀ i, t' i = times (Fin.cast h i)) :
    (finiteTimeKernel P t').map (fun p (i : Fin n) => p (Fin.cast h.symm i)) =
      finiteTimeKernel P times := by
  subst h
  have : t' = times := by
    ext i
    simp [ht i]
  subst this
  simp only [Fin.cast_eq_self]
  exact Kernel.map_id _

omit [LocallyCompactSpace alpha] in
theorem AuxB_rational (hK : P.KolmogorovRegular hP) {n : ℕ} (times : FiniteOrderedTimes n)
    (r : Fin n → DenseTime) (hr : ∀ i, times i = DenseTime.castOrderEmbedding (r i)) :
    (continuousProcess P hP).map (ContinuousPath.finiteEvaluation (fun i ↦ times i)) =
      finiteTimeKernel P times := by
  classical
  set J : Finset DenseTime := Finset.univ.image r with hJ
  set S : Finset NNReal := denseTimePhysicalSet J with hS
  have hmem : ∀ i, times i ∈ S := by
    intro i
    simp only [hS, denseTimePhysicalSet, Finset.mem_map, hJ, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨r i, ⟨i, rfl⟩, (hr i).symm⟩
  have hrinj : Function.Injective r := by
    intro i j hij
    apply times.injective
    rw [hr i, hr j, hij]
  have hcard : S.card = n := by
    simp only [hS, denseTimePhysicalSet, Finset.card_map, hJ]
    rw [Finset.card_image_of_injective _ hrinj, Finset.card_univ, Fintype.card_fin]
  have hu : ∀ j : Fin S.card, S.orderEmbOfFin rfl j = times (Fin.cast hcard j) := by
    have := Finset.orderEmbOfFin_unique (s := S) (k := S.card) rfl
      (f := fun j : Fin S.card => times (Fin.cast hcard j)) (fun j => hmem _)
      (fun a b hab => times.strictMono (by simpa using hab))
    intro j
    rw [← this]
  let e : (S → alpha) → (Fin n → alpha) := fun g i => g ⟨times i, hmem i⟩
  have he : Measurable e := by
    rw [measurable_pi_iff]; intro i; exact measurable_pi_apply _
  have hEv : Measurable (ContinuousPath.finsetEvaluation (alpha := alpha) S) := by
    rw [measurable_pi_iff]
    intro t
    rw [BorelSpace.measurable_eq (α := alpha)]
    exact (ContinuousPath.continuous_eval (alpha := alpha) (t : NNReal)).borel_measurable
  have hfun : ContinuousPath.finiteEvaluation (α := alpha) (fun i ↦ times i) =
      e ∘ ContinuousPath.finsetEvaluation S := rfl
  have hb := _root_.MarkovProcess.SubMarkovKernelSemigroup.IsConservative.p2m_embedded_b819d8df72e216cf
    P hP (ContinuousMap.const NNReal (Classical.arbitrary alpha)) hK J
  have hb' : (continuousProcess P hP).map (ContinuousPath.finsetEvaluation S) =
      finiteSetKernel P S := hb
  rw [hfun, Kernel.map_comp_right _ hEv he, hb', finiteSetKernel_eq_map,
    ← Kernel.map_comp_right _ (measurable_orderedPathToFiniteSet S) he]
  have hcomp : e ∘ orderedPathToFiniteSet S = fun p (i : Fin n) => p (Fin.cast hcard.symm i) := by
    funext p i
    simp only [Function.comp_apply, e, orderedPathToFiniteSet]
    congr 1
    apply (S.orderIsoOfFin rfl).injective
    rw [OrderIso.apply_symm_apply]
    apply Subtype.ext
    rw [Finset.coe_orderIsoOfFin_apply, hu]
    simp
  rw [hcomp]
  exact AuxB_reindex P hcard times (finiteSetTimes S) (fun j => hu j)

theorem AuxB_approx {n : ℕ} (times : FiniteOrderedTimes n) :
    ∃ q : ℕ → Fin n → DenseTime, (∀ k, StrictMono fun i => DenseTime.castOrderEmbedding (q k i)) ∧
      ∀ i, Filter.Tendsto (fun k => DenseTime.castOrderEmbedding (q k i)) Filter.atTop
        (nhds (times i)) := by
  classical
  let u : Fin n → NNReal := fun i =>
    if h : (i : ℕ) + 1 < n then times ⟨i + 1, h⟩ else times i + 1
  have hu : ∀ i, times i < u i := by
    intro i
    simp only [u]
    split_ifs with h
    · exact times.strictMono (Fin.lt_def.2 (by simp))
    · exact lt_add_one _
  have hub : ∀ a b : Fin n, a < b → u a ≤ times b := by
    intro a b hab
    have h : (a : ℕ) + 1 < n := by have := b.2; rw [Fin.lt_def] at hab; omega
    simp only [u, dif_pos h]
    exact times.monotone (Fin.le_def.2 (by rw [Fin.lt_def] at hab; simp; omega))
  have hex : ∀ (k : ℕ) (i : Fin n), ∃ r : DenseTime, times i < DenseTime.castOrderEmbedding r ∧
      DenseTime.castOrderEmbedding r < min (u i) (times i + 1 / ((k : NNReal) + 1)) := by
    intro k i
    apply DenseTime.exists_cast_btwn
    refine lt_min (hu i) ?_
    have : (0 : NNReal) < 1 / ((k : NNReal) + 1) := by positivity
    exact lt_add_of_pos_right _ this
  choose q hq1 hq2 using hex
  refine ⟨q, ?_, ?_⟩
  · intro k a b hab
    calc DenseTime.castOrderEmbedding (q k a) < u a := (lt_min_iff.1 (hq2 k a)).1
      _ ≤ times b := hub a b hab
      _ < _ := hq1 k b
  · intro i
    have hup : Filter.Tendsto (fun k : ℕ => times i + 1 / ((k : NNReal) + 1)) Filter.atTop
        (nhds (times i)) := by
      have h0 : Filter.Tendsto (fun k : ℕ => 1 / ((k : NNReal) + 1)) Filter.atTop (nhds 0) := by
        rw [← NNReal.tendsto_coe]
        have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using h1
      simpa using tendsto_const_nhds.add h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun k => (hq1 k i).le) (fun k => (hq2 k i).le.trans (min_le_right _ _))

open MarkovProcess.SubMarkovKernelSemigroup in
theorem AuxB_ordered
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) {n : ℕ}
    (times : FiniteOrderedTimes n) :
    (continuousProcess P hP).map (ContinuousPath.finiteEvaluation (fun i ↦ times i)) =
      finiteTimeKernel P times := by
  obtain ⟨q, hqm, hql⟩ := AuxB_approx times
  let tk : ℕ → FiniteOrderedTimes n := fun k => OrderEmbedding.ofStrictMono _ (hqm k)
  have htk : ∀ k i, tk k i = DenseTime.castOrderEmbedding (q k i) := fun k i => rfl
  have hEv : ∀ τ : Fin n → NNReal, Measurable (ContinuousPath.finiteEvaluation (α := alpha) τ) :=
    fun τ => (ContinuousPath.continuous_finiteEvaluation τ).measurable
  haveI : IsMarkovKernel (finiteTimeKernel P times) :=
    IsConservative.isMarkovKernel_finiteTimeKernel P hP times
  ext x : 1
  rw [Kernel.map_apply _ (hEv _)]
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have h1 := hFeller.p2m_embedded_2e9adf8c161c36f0 hP (times := tk) (times₀ := times)
    (x := fun _ => x) (l := Filter.atTop) (fun i => by simpa [htk] using hql i)
    tendsto_const_nhds f
  refine tendsto_nhds_unique ?_ h1
  have heq : ∀ k, ∫ path, f path ∂finiteTimeKernel P (tk k) x =
      ∫ ω, f (ContinuousPath.finiteEvaluation (fun i => tk k i) ω) ∂(continuousProcess P hP x) := by
    intro k
    rw [← AuxB_rational P hP hK (tk k) (q k) (htk k), Kernel.map_apply _ (hEv _),
      integral_map (hEv _).aemeasurable (map_continuous f).aestronglyMeasurable]
  simp_rw [heq]
  rw [integral_map (hEv _).aemeasurable (map_continuous f).aestronglyMeasurable]
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  refine tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun k => (f.continuous.comp (ContinuousPath.continuous_finiteEvaluation _)).aestronglyMeasurable)
    (integrable_const _) (fun k => Filter.Eventually.of_forall fun ω => hC _)
    (Filter.Eventually.of_forall fun ω => ?_)
  apply (f.continuous.tendsto _).comp
  apply tendsto_pi_nhds.2
  intro i
  exact (ω.continuous.tendsto _).comp (by simpa [htk] using hql i)

omit [LocallyCompactSpace alpha] in
theorem AuxB_finsetEval_eq (I : Finset NNReal) :
    ContinuousPath.finsetEvaluation (alpha := alpha) I =
      orderedPathToFiniteSet I ∘ ContinuousPath.finiteEvaluation (fun i ↦ finiteSetTimes I i) := by
  funext path t
  simp only [Function.comp_apply, orderedPathToFiniteSet, ContinuousPath.finiteEvaluation,
    finiteSetTimes]
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

theorem AuxB_finset (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (I : Finset NNReal) :
    (continuousProcess P hP).map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I := by
  rw [AuxB_finsetEval_eq, Kernel.map_comp_right _
    (ContinuousPath.continuous_finiteEvaluation _).measurable
    (measurable_orderedPathToFiniteSet I), AuxB_ordered P hP hFeller hK, finiteSetKernel_eq_map]

end AuxSec

open MarkovProcess in
theorem solution (I : Finset NNReal) :
    brownianMotion.map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel heatSemigroup I := by
  have hK : heatSemigroup.KolmogorovRegular isConservative_heatSemigroup :=
    SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments heatSemigroup
      isConservative_heatSemigroup MarkovProcess.p2m_embedded_d699d49b7a4121f2
  exact AuxB_finset heatSemigroup isConservative_heatSemigroup
    isFellerKernelSemigroup_heatSemigroup hK I
