-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuous_integral_eval_continuousProcess
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:03:30.480267+00:00
-- url     : https://prove2.me/submissions/9785bcde-16ef-414a-ab94-7eff39994d30

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
import Definitions.Def_MarkovProcess_V3H_Feller_FiniteSetCompactTestContinuity_012434c8
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
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
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Tight
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

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Measurable and continuous dependence on the starting point

Two regularity statements for the continuous-path process of a conservative sub-Markov kernel
semigroup, both in the starting point.

*Measurability.*  For a strongly measurable functional `F` of the path, the expectation
`x ↦ ∫ F d(continuousProcess P hP x)` is strongly measurable, hence measurable into a Borel
target: `IsConservative.stronglyMeasurable_integral_continuousProcess` and
`IsConservative.measurable_integral_continuousProcess`.  The same holds for the two functionals
that the strong Markov property produces, the shifted path and the state at a finite stopping
time: `IsConservative.measurable_integral_shift_stoppingTime_continuousProcess` and
`IsConservative.measurable_integral_eval_stoppingTime_continuousProcess`.

*Continuity.*  For a Feller semigroup the finite-dimensional laws depend weakly continuously on
the starting point: `IsFellerKernelSemigroup.continuous_integral_boundedContinuous_finiteSetKernel`
upgrades compact-test continuity to all bounded continuous test functions.  The
upgrade is a tightness argument: a finite-dimensional law on a Polish coordinate space is tight,
so a compactly supported continuous cutoff `g` with `1_K ≤ g ≤ 1` captures all but `epsilon` of the
mass at the reference starting point, the truncated integral `∫ f * g` is continuous by the
compact-test theorem, and the discarded part is bounded by `‖f‖ * (1 - ∫ g)`, itself continuous
and small.  On the process this reads as continuity of cylinder expectations,
`IsFellerKernelSemigroup.continuous_integral_finsetEvaluation_continuousProcess`, with the
one-time case `IsFellerKernelSemigroup.continuous_integral_eval_continuousProcess`.

Nothing here asserts weak continuity of the full path law `x ↦ continuousProcess P hP x` on path
space; that needs tightness on path space itself, which is not proved here.  No statement covers
a stopping time that can be infinite.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction CompactlySupported NNReal

namespace MarkovProcess


namespace SubMarkovKernelSemigroup

section BoundedContinuousTest

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [SecondCountableTopology alpha] [LocallyCompactSpace alpha]



end BoundedContinuousTest

noncomputable section Process

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

section Measurability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



variable [MeasurableSpace E] [BorelSpace E]







end Measurability

section Continuity

variable [LocallyCompactSpace alpha]





end Continuity

end Process

end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Measurable and continuous dependence on the starting point

Two regularity statements for the continuous-path process of a conservative sub-Markov kernel
semigroup, both in the starting point.

*Measurability.*  For a strongly measurable functional `F` of the path, the expectation
`x ↦ ∫ F d(continuousProcess P hP x)` is strongly measurable, hence measurable into a Borel
target: `IsConservative.stronglyMeasurable_integral_continuousProcess` and
`IsConservative.measurable_integral_continuousProcess`.  The same holds for the two functionals
that the strong Markov property produces, the shifted path and the state at a finite stopping
time: `IsConservative.measurable_integral_shift_stoppingTime_continuousProcess` and
`IsConservative.measurable_integral_eval_stoppingTime_continuousProcess`.

*Continuity.*  For a Feller semigroup the finite-dimensional laws depend weakly continuously on
the starting point: `IsFellerKernelSemigroup.continuous_integral_boundedContinuous_finiteSetKernel`
upgrades compact-test continuity to all bounded continuous test functions.  The
upgrade is a tightness argument: a finite-dimensional law on a Polish coordinate space is tight,
so a compactly supported continuous cutoff `g` with `1_K ≤ g ≤ 1` captures all but `epsilon` of the
mass at the reference starting point, the truncated integral `∫ f * g` is continuous by the
compact-test theorem, and the discarded part is bounded by `‖f‖ * (1 - ∫ g)`, itself continuous
and small.  On the process this reads as continuity of cylinder expectations,
`IsFellerKernelSemigroup.continuous_integral_finsetEvaluation_continuousProcess`, with the
one-time case `IsFellerKernelSemigroup.continuous_integral_eval_continuousProcess`.

Nothing here asserts weak continuity of the full path law `x ↦ continuousProcess P hP x` on path
space; that needs tightness on path space itself, which is not proved here.  No statement covers
a stopping time that can be infinite.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction CompactlySupported NNReal






open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



variable [LocallyCompactSpace alpha]





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


omit [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha] in
theorem AuxF_cc (hFeller : P.IsFellerKernelSemigroup) (t : NNReal) (h : alpha →ᵇ ℝ)
    (hc : HasCompactSupport h) : Continuous fun x => ∫ y, h y ∂(P t x) := by
  let h0 : ZeroAtInftyContinuousMap alpha ℝ := ⟨h.toContinuousMap, hc.is_zero_at_infty⟩
  have := (hFeller.c0Semigroup t h0).continuous
  convert this using 1
  funext x
  rfl

include hP in
theorem AuxF_cb (hFeller : P.IsFellerKernelSemigroup) (t : NNReal) (g : alpha →ᵇ ℝ) :
    Continuous fun x => ∫ y, g y ∂(P t x) := by
  haveI : ∀ x, IsProbabilityMeasure (P t x) := fun x => ⟨hP t x⟩
  rw [continuous_iff_continuousAt]
  intro x0
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set C : ℝ := ‖g‖ + 1 with hC
  have hCpos : 0 < C := by positivity
  set δ : ℝ := ε / (4 * C) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨K, -, hK, hKμ⟩ := (MeasurableSet.univ (α := alpha)).exists_isCompact_diff_lt
    (measure_ne_top (P t x0) Set.univ) (ENNReal.ofReal_pos.mpr hδpos).ne'
  obtain ⟨φ, hφK, -, hφcs, hφI⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty
    (Set.disjoint_empty K)
  let φb : alpha →ᵇ ℝ := BoundedContinuousFunction.mkOfBound φ 1
    (fun x y => Real.dist_le_of_mem_Icc_01 (hφI x) (hφI y))
  have hφb : ∀ x, φb x = φ x := fun x => rfl
  have hcs1 : HasCompactSupport φb := hφcs
  have hcs2 : HasCompactSupport (g * φb) := by
    have : (⇑(g * φb)) = fun x => g x * φ x := rfl
    rw [this]; exact hφcs.mul_left
  have hc1 := AuxF_cc P hFeller t φb hcs1
  have hc2 := AuxF_cc P hFeller t (g * φb) hcs2
  -- tail estimate
  have htail : ∀ x, |∫ y, g y ∂(P t x) - ∫ y, (g * φb) y ∂(P t x)| ≤
      ‖g‖ * (1 - ∫ y, φb y ∂(P t x)) := by
    intro x
    rw [← integral_sub (g.integrable _) ((g * φb).integrable _)]
    have hφint := φb.integrable (P t x)
    calc |∫ y, g y - (g * φb) y ∂(P t x)| ≤ ∫ y, |g y - (g * φb) y| ∂(P t x) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ y, ‖g‖ * (1 - φb y) ∂(P t x) := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
            ((integrable_const _).sub hφint |>.const_mul _)
          refine Eventually.of_forall fun y => ?_
          show |g y - (g * φb) y| ≤ ‖g‖ * (1 - φb y)
          have e : (g * φb) y = g y * φ y := rfl
          rw [e, hφb]
          have hg : |g y| ≤ ‖g‖ := by simpa [Real.norm_eq_abs] using g.norm_coe_le_norm y
          have h1 : 0 ≤ 1 - φ y := by linarith [(hφI y).2]
          rw [show g y - g y * φ y = g y * (1 - φ y) by ring, abs_mul, abs_of_nonneg h1]
          exact mul_le_mul_of_nonneg_right hg h1
      _ = ‖g‖ * (1 - ∫ y, φb y ∂(P t x)) := by
          rw [integral_const_mul, integral_sub (integrable_const _) hφint]
          simp
  have h0 : 1 - ∫ y, φb y ∂(P t x0) ≤ δ := by
    have : ∫ y, (1 - φb y) ∂(P t x0) ≤ (P t x0).real (Set.univ \ K) := by
      rw [← integral_indicator_one (MeasurableSet.univ.diff hK.measurableSet)]
      apply integral_mono ((integrable_const _).sub (φb.integrable _))
        ((integrable_const _).indicator (MeasurableSet.univ.diff hK.measurableSet))
      intro y
      by_cases hy : y ∈ K
      · simp [Set.indicator, hy, hφb, hφK hy]
      · simp only [Set.indicator, Set.mem_diff, Set.mem_univ, hy, not_false_eq_true, and_self,
          if_true, Pi.one_apply]
        show 1 - φb y ≤ 1
        rw [hφb]
        linarith [(hφI y).1]
    rw [integral_sub (integrable_const _) (φb.integrable _)] at this
    simp only [integral_const, smul_eq_mul, mul_one, measureReal_def, measure_univ,
      ENNReal.toReal_one] at this
    refine this.trans ?_
    rw [← ENNReal.ofReal_toReal (measure_ne_top (P t x0) _)] at hKμ
    exact (ENNReal.ofReal_lt_ofReal_iff hδpos).mp hKμ |>.le
  have e1 := Metric.tendsto_nhds.mp (hc1.tendsto x0) δ hδpos
  have e2 := Metric.tendsto_nhds.mp (hc2.tendsto x0) δ hδpos
  filter_upwards [e1, e2] with x hx1 hx2
  rw [Real.dist_eq] at hx1 hx2 ⊢
  have t1 := htail x
  have t0 := htail x0
  have hgn : 0 ≤ ‖g‖ := norm_nonneg _
  have hφx : 1 - ∫ y, φb y ∂(P t x) ≤ 2 * δ := by
    have := (abs_lt.mp hx1).1; linarith
  have hb1 : ‖g‖ * (1 - ∫ y, φb y ∂(P t x)) ≤ ‖g‖ * (2 * δ) := mul_le_mul_of_nonneg_left hφx hgn
  have hb0 : ‖g‖ * (1 - ∫ y, φb y ∂(P t x0)) ≤ ‖g‖ * δ := mul_le_mul_of_nonneg_left h0 hgn
  have hgδ : ‖g‖ * δ ≤ ε / 4 := by
    rw [hδ, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hδ4 : δ ≤ ε / 4 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc |∫ y, g y ∂(P t x) - ∫ y, g y ∂(P t x0)|
      ≤ |∫ y, g y ∂(P t x) - ∫ y, (g * φb) y ∂(P t x)| +
        |∫ y, (g * φb) y ∂(P t x) - ∫ y, (g * φb) y ∂(P t x0)| +
        |∫ y, (g * φb) y ∂(P t x0) - ∫ y, g y ∂(P t x0)| := by
          have := abs_sub_le (∫ y, g y ∂(P t x)) (∫ y, (g * φb) y ∂(P t x)) (∫ y, g y ∂(P t x0))
          have := abs_sub_le (∫ y, (g * φb) y ∂(P t x)) (∫ y, (g * φb) y ∂(P t x0)) (∫ y, g y ∂(P t x0))
          linarith
    _ < ε := by
          rw [abs_sub_comm (∫ y, (g * φb) y ∂(P t x0))]
          linarith


open MarkovProcess.SubMarkovKernelSemigroup in
theorem solution
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (t : NNReal)
    (g : alpha →ᵇ ℝ) :
    Continuous fun x ↦ ∫ omega, g (omega t) ∂(continuousProcess P hP x) := by
  let τ : FiniteOrderedTimes 1 := OrderEmbedding.ofStrictMono (fun _ : Fin 1 => t)
    (fun a b h => absurd h (by rw [Subsingleton.elim a b]; exact lt_irrefl b))
  have hFE : Measurable (ContinuousPath.finiteEvaluation (α := alpha) (fun i ↦ τ i)) :=
    (ContinuousPath.continuous_finiteEvaluation _).measurable
  have hmap : (continuousProcess P hP).map (fun omega : ContinuousPath alpha => omega t) = P t := by
    have : (fun omega : ContinuousPath alpha => omega t) =
        (fun p : Fin 1 → alpha => p 0) ∘ ContinuousPath.finiteEvaluation (fun i ↦ τ i) := by
      funext omega; rfl
    rw [this, Kernel.map_comp_right _ hFE (measurable_pi_apply 0), AuxB_ordered P hP hFeller hK,
      _root_.MarkovProcess.SubMarkovKernelSemigroup.p2m_embedded_5bab9ee57d353238]
    rfl
  have hm : Measurable (fun omega : ContinuousPath alpha => omega t) :=
    (continuous_eval_const t).measurable
  have : (fun x ↦ ∫ omega, g (omega t) ∂(continuousProcess P hP x)) =
      fun x => ∫ y, g y ∂(P t x) := by
    funext x
    rw [← hmap, Kernel.map_apply _ hm, integral_map hm.aemeasurable g.continuous.aestronglyMeasurable]
  rw [this]
  exact AuxF_cb P hP hFeller t g
