-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.tendsto_integral_eval_continuousProcess
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:05:30.368872+00:00
-- url     : https://prove2.me/submissions/21ff6607-d3c5-47fe-99f2-b70a09727a4d

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
import Definitions.Def_MarkovProcess_V3H_Feller_FiniteTimeConvergence_4d25bc20
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelCompactTestTransport_3904fd05
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
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
# Convergence of the finite-dimensional distributions of Feller processes

Let `P i` be conservative Feller kernel semigroups and `Q` one more such semigroup, with
continuous-path processes `continuousProcess (P i)` and `continuousProcess Q`.  If the `C₀`
semigroups converge strongly -- by `Semigroup/TrotterKato.lean` this follows from convergence of
their resolvents at one
positive shift -- then the finite-dimensional distributions of the processes converge weakly from
every starting point: for every finite set `I` of times and every bounded continuous functional
of the coordinates at those times, the expectations converge.

The route is the identification of the finite-dimensional distributions with the finite-set
kernels (`continuousProcess_map_finiteEvaluation`), where the statement is
`Feller/FiniteSetConvergence.lean`.

Main results: `tendsto_integral_finsetEvaluation_continuousProcess`,
`tendsto_integral_eval_continuousProcess`.

Convergence of the finite-dimensional distributions is not convergence on path space, which needs
in addition a tightness estimate for the family of laws; that is not asserted here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]
variable {iota : Type*} {l : Filter iota}
variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}





end

end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Convergence of the finite-dimensional distributions of Feller processes

Let `P i` be conservative Feller kernel semigroups and `Q` one more such semigroup, with
continuous-path processes `continuousProcess (P i)` and `continuousProcess Q`.  If the `C₀`
semigroups converge strongly -- by `Semigroup/TrotterKato.lean` this follows from convergence of
their resolvents at one
positive shift -- then the finite-dimensional distributions of the processes converge weakly from
every starting point: for every finite set `I` of times and every bounded continuous functional
of the coordinates at those times, the expectations converge.

The route is the identification of the finite-dimensional distributions with the finite-set
kernels (`continuousProcess_map_finiteEvaluation`), where the statement is
`Feller/FiniteSetConvergence.lean`.

Main results: `tendsto_integral_finsetEvaluation_continuousProcess`,
`tendsto_integral_eval_continuousProcess`.

Convergence of the finite-dimensional distributions is not convergence on path space, which needs
in addition a tightness estimate for the family of laws; that is not asserted here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction NNReal ZeroAtInfty



open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]
variable {iota : Type*} {l : Filter iota}
variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}





section AuxSecW
variable {α₁ : Type*} [MetricSpace α₁] [CompleteSpace α₁]
  [MeasurableSpace α₁] [BorelSpace α₁] [SecondCountableTopology α₁]
  [Nonempty α₁] [LocallyCompactSpace α₁]
variable (P₁ : MarkovProcess.SubMarkovKernelSemigroup α₁) (hP₁ : P₁.IsConservative)
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup

open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup

omit [CompleteSpace α₁] [SecondCountableTopology α₁] [Nonempty α₁] [LocallyCompactSpace α₁] in
theorem AuxB_reindex {n m : ℕ} (h : m = n) (times : FiniteOrderedTimes n)
    (t' : FiniteOrderedTimes m) (ht : ∀ i, t' i = times (Fin.cast h i)) :
    (finiteTimeKernel P₁ t').map (fun p (i : Fin n) => p (Fin.cast h.symm i)) =
      finiteTimeKernel P₁ times := by
  subst h
  have : t' = times := by
    ext i
    simp [ht i]
  subst this
  simp only [Fin.cast_eq_self]
  exact Kernel.map_id _

omit [LocallyCompactSpace α₁] in
theorem AuxB_rational (hK : P₁.KolmogorovRegular hP₁) {n : ℕ} (times : FiniteOrderedTimes n)
    (r : Fin n → DenseTime) (hr : ∀ i, times i = DenseTime.castOrderEmbedding (r i)) :
    (continuousProcess P₁ hP₁).map (ContinuousPath.finiteEvaluation (fun i ↦ times i)) =
      finiteTimeKernel P₁ times := by
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
  let e : (S → α₁) → (Fin n → α₁) := fun g i => g ⟨times i, hmem i⟩
  have he : Measurable e := by
    rw [measurable_pi_iff]; intro i; exact measurable_pi_apply _
  have hEv : Measurable (ContinuousPath.finsetEvaluation (alpha := α₁) S) := by
    rw [measurable_pi_iff]
    intro t
    rw [BorelSpace.measurable_eq (α := α₁)]
    exact (ContinuousPath.continuous_eval (alpha := α₁) (t : NNReal)).borel_measurable
  have hfun : ContinuousPath.finiteEvaluation (α := α₁) (fun i ↦ times i) =
      e ∘ ContinuousPath.finsetEvaluation S := rfl
  have hb := _root_.MarkovProcess.SubMarkovKernelSemigroup.IsConservative.p2m_embedded_b819d8df72e216cf
    P₁ hP₁ (ContinuousMap.const NNReal (Classical.arbitrary α₁)) hK J
  have hb' : (continuousProcess P₁ hP₁).map (ContinuousPath.finsetEvaluation S) =
      finiteSetKernel P₁ S := hb
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
  exact AuxB_reindex P₁ hcard times (finiteSetTimes S) (fun j => hu j)

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
    (hFeller : P₁.IsFellerKernelSemigroup) (hK : P₁.KolmogorovRegular hP₁) {n : ℕ}
    (times : FiniteOrderedTimes n) :
    (continuousProcess P₁ hP₁).map (ContinuousPath.finiteEvaluation (fun i ↦ times i)) =
      finiteTimeKernel P₁ times := by
  obtain ⟨q, hqm, hql⟩ := AuxB_approx times
  let tk : ℕ → FiniteOrderedTimes n := fun k => OrderEmbedding.ofStrictMono _ (hqm k)
  have htk : ∀ k i, tk k i = DenseTime.castOrderEmbedding (q k i) := fun k i => rfl
  have hEv : ∀ τ : Fin n → NNReal, Measurable (ContinuousPath.finiteEvaluation (α := α₁) τ) :=
    fun τ => (ContinuousPath.continuous_finiteEvaluation τ).measurable
  haveI : IsMarkovKernel (finiteTimeKernel P₁ times) :=
    IsConservative.isMarkovKernel_finiteTimeKernel P₁ hP₁ times
  ext x : 1
  rw [Kernel.map_apply _ (hEv _)]
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have h1 := hFeller.p2m_embedded_2e9adf8c161c36f0 hP₁ (times := tk) (times₀ := times)
    (x := fun _ => x) (l := Filter.atTop) (fun i => by simpa [htk] using hql i)
    tendsto_const_nhds f
  refine tendsto_nhds_unique ?_ h1
  have heq : ∀ k, ∫ path, f path ∂finiteTimeKernel P₁ (tk k) x =
      ∫ ω, f (ContinuousPath.finiteEvaluation (fun i => tk k i) ω) ∂(continuousProcess P₁ hP₁ x) := by
    intro k
    rw [← AuxB_rational P₁ hP₁ hK (tk k) (q k) (htk k), Kernel.map_apply _ (hEv _),
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

omit [LocallyCompactSpace α₁] in
theorem AuxB_finsetEval_eq (I : Finset NNReal) :
    ContinuousPath.finsetEvaluation (alpha := α₁) I =
      orderedPathToFiniteSet I ∘ ContinuousPath.finiteEvaluation (fun i ↦ finiteSetTimes I i) := by
  funext path t
  simp only [Function.comp_apply, orderedPathToFiniteSet, ContinuousPath.finiteEvaluation,
    finiteSetTimes]
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

theorem AuxB_finset (hFeller : P₁.IsFellerKernelSemigroup) (hK : P₁.KolmogorovRegular hP₁)
    (I : Finset NNReal) :
    (continuousProcess P₁ hP₁).map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P₁ I := by
  rw [AuxB_finsetEval_eq, Kernel.map_comp_right _
    (ContinuousPath.continuous_finiteEvaluation _).measurable
    (measurable_orderedPathToFiniteSet I), AuxB_ordered P₁ hP₁ hFeller hK, finiteSetKernel_eq_map]

omit [Nonempty α₁] in
theorem AuxF_weak {ι : Type*} {l : Filter ι} (μs : ι → Measure α₁) (μ : Measure α₁)
    [∀ i, IsProbabilityMeasure (μs i)] [IsProbabilityMeasure μ]
    (hcc : ∀ h : α₁ →ᵇ ℝ, HasCompactSupport h →
      Tendsto (fun i => ∫ y, h y ∂(μs i)) l (nhds (∫ y, h y ∂μ)))
    (g : α₁ →ᵇ ℝ) : Tendsto (fun i => ∫ y, g y ∂(μs i)) l (nhds (∫ y, g y ∂μ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set C : ℝ := ‖g‖ + 1 with hC
  have hCpos : 0 < C := by positivity
  set δ : ℝ := ε / (4 * C) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨K, -, hK, hKμ⟩ := (MeasurableSet.univ (α := α₁)).exists_isCompact_diff_lt
    (measure_ne_top μ Set.univ) (ENNReal.ofReal_pos.mpr hδpos).ne'
  obtain ⟨φ, hφK, -, hφcs, hφI⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty
    (Set.disjoint_empty K)
  let φb : α₁ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound φ 1
    (fun x y => Real.dist_le_of_mem_Icc_01 (hφI x) (hφI y))
  have hφb : ∀ x, φb x = φ x := fun x => rfl
  have hcs1 : HasCompactSupport φb := hφcs
  have hcs2 : HasCompactSupport (g * φb) := by
    have : (⇑(g * φb)) = fun x => g x * φ x := rfl
    rw [this]; exact hφcs.mul_left
  have hc1 := hcc φb hcs1
  have hc2 := hcc (g * φb) hcs2
  have htail : ∀ (ν : Measure α₁) [IsProbabilityMeasure ν], |∫ y, g y ∂ν - ∫ y, (g * φb) y ∂ν| ≤
      ‖g‖ * (1 - ∫ y, φb y ∂ν) := by
    intro ν _
    rw [← integral_sub (g.integrable _) ((g * φb).integrable _)]
    have hφint := φb.integrable ν
    calc |∫ y, g y - (g * φb) y ∂ν| ≤ ∫ y, |g y - (g * φb) y| ∂ν :=
          abs_integral_le_integral_abs
      _ ≤ ∫ y, ‖g‖ * (1 - φb y) ∂ν := by
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
      _ = ‖g‖ * (1 - ∫ y, φb y ∂ν) := by
          rw [integral_const_mul, integral_sub (integrable_const _) hφint]
          simp
  have h0 : 1 - ∫ y, φb y ∂μ ≤ δ := by
    have : ∫ y, (1 - φb y) ∂μ ≤ μ.real (Set.univ \ K) := by
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
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)] at hKμ
    exact (ENNReal.ofReal_lt_ofReal_iff hδpos).mp hKμ |>.le
  have e1 := Metric.tendsto_nhds.mp hc1 δ hδpos
  have e2 := Metric.tendsto_nhds.mp hc2 δ hδpos
  filter_upwards [e1, e2] with x hx1 hx2
  rw [Real.dist_eq] at hx1 hx2 ⊢
  have t1 := htail (μs x)
  have t0 := htail μ
  have hgn : 0 ≤ ‖g‖ := norm_nonneg _
  have hφx : 1 - ∫ y, φb y ∂(μs x) ≤ 2 * δ := by
    have := (abs_lt.mp hx1).1; linarith
  have hb1 : ‖g‖ * (1 - ∫ y, φb y ∂(μs x)) ≤ ‖g‖ * (2 * δ) := mul_le_mul_of_nonneg_left hφx hgn
  have hb0 : ‖g‖ * (1 - ∫ y, φb y ∂μ) ≤ ‖g‖ * δ := mul_le_mul_of_nonneg_left h0 hgn
  have hgδ : ‖g‖ * δ ≤ ε / 4 := by
    rw [hδ, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hδ4 : δ ≤ ε / 4 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc |∫ y, g y ∂(μs x) - ∫ y, g y ∂μ|
      ≤ |∫ y, g y ∂(μs x) - ∫ y, (g * φb) y ∂(μs x)| +
        |∫ y, (g * φb) y ∂(μs x) - ∫ y, (g * φb) y ∂μ| +
        |∫ y, (g * φb) y ∂μ - ∫ y, g y ∂μ| := by
          have := abs_sub_le (∫ y, g y ∂(μs x)) (∫ y, (g * φb) y ∂(μs x)) (∫ y, g y ∂μ)
          have := abs_sub_le (∫ y, (g * φb) y ∂(μs x)) (∫ y, (g * φb) y ∂μ) (∫ y, g y ∂μ)
          linarith
    _ < ε := by
          rw [abs_sub_comm (∫ y, (g * φb) y ∂μ)]
          linarith

theorem AuxF_marg (hFeller : P₁.IsFellerKernelSemigroup) (hK : P₁.KolmogorovRegular hP₁)
    (t : NNReal) :
    (continuousProcess P₁ hP₁).map (fun omega : ContinuousPath α₁ => omega t) = P₁ t := by
  let τ : FiniteOrderedTimes 1 := OrderEmbedding.ofStrictMono (fun _ : Fin 1 => t)
    (fun a b h => absurd h (by rw [Subsingleton.elim a b]; exact lt_irrefl b))
  have hFE : Measurable (ContinuousPath.finiteEvaluation (α := α₁) (fun i ↦ τ i)) :=
    (ContinuousPath.continuous_finiteEvaluation _).measurable
  have : (fun omega : ContinuousPath α₁ => omega t) =
      (fun p : Fin 1 → α₁ => p 0) ∘ ContinuousPath.finiteEvaluation (fun i ↦ τ i) := by
    funext omega; rfl
  rw [this, Kernel.map_comp_right _ hFE (measurable_pi_apply 0), AuxB_ordered P₁ hP₁ hFeller hK,
    _root_.MarkovProcess.SubMarkovKernelSemigroup.p2m_embedded_5bab9ee57d353238]
  rfl

end AuxSecW

open MarkovProcess.SubMarkovKernelSemigroup in
theorem solution
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hPK : ∀ i, (P i).KolmogorovRegular (hPc i))
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative) (hQK : Q.KolmogorovRegular hQc)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    (t : NNReal) (g : alpha →ᵇ ℝ) (x : alpha) :
    Tendsto (fun i ↦ ∫ omega, g (omega t) ∂(continuousProcess (P i) (hPc i) x)) l
      (nhds (∫ omega, g (omega t) ∂(continuousProcess Q hQc x))) := by
  have hm : Measurable (fun omega : ContinuousPath alpha => omega t) :=
    (continuous_eval_const t).measurable
  have hrw : ∀ (R : SubMarkovKernelSemigroup alpha) (hR : R.IsConservative)
      (hRF : R.IsFellerKernelSemigroup) (hRK : R.KolmogorovRegular hR),
      ∫ omega, g (omega t) ∂(continuousProcess R hR x) = ∫ y, g y ∂(R t x) := by
    intro R hR hRF hRK
    rw [← AuxF_marg R hR hRF hRK t, Kernel.map_apply _ hm,
      integral_map hm.aemeasurable g.continuous.aestronglyMeasurable]
  simp_rw [hrw _ _ (hP _) (hPK _), hrw Q hQc hQ hQK]
  haveI : ∀ i, IsProbabilityMeasure ((P i) t x) := fun i => ⟨hPc i t x⟩
  haveI : IsProbabilityMeasure (Q t x) := ⟨hQc t x⟩
  refine AuxF_weak (fun i => (P i) t x) (Q t x) (fun h hc => ?_) g
  let h0 : C₀(alpha, ℝ) := ⟨h.toContinuousMap, hc.is_zero_at_infty⟩
  have hev : Continuous fun F : C₀(alpha, ℝ) => F x :=
    ((continuous_eval_const x : Continuous fun G : alpha →ᵇ ℝ => G x).comp
      ZeroAtInftyContinuousMap.isometry_toBCF.continuous :)
  exact (hev.tendsto _).comp (hconv t h0)
