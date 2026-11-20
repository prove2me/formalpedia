-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_map_shift
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:06:52.259404+00:00
-- url     : https://prove2.me/submissions/50631ed2-d181-4726-9edd-b373ace8ff47

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_DenseTime_TwoPointMarginals_b3a3d14b
import Definitions.Def_MarkovProcess_V3H_Feller_BackwardC0Integral_1512e54f
import Definitions.Def_MarkovProcess_V3H_Feller_DensePhysicalFiniteSetContinuity_75f8b26c
import Definitions.Def_MarkovProcess_V3H_FiniteTime_CoordinateProductActiveReduction_0fcd6a29
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelCompactTestTransport_3904fd05
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelShift_14b03019
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelEquivariance_10113825
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelRestriction_041bf9e5
import Definitions.Def_MarkovProcess_V3H_Kernel_FiniteRestrictionIdentification_619c5320
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcess_caf2584d
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_Polish_87f91693
import Definitions.Def_MarkovProcess_V3H_Path_RandomShiftMeasurability_fbe17c52
import Definitions.Def_MarkovProcess_V3H_Path_ShiftCompactTestConvergence_fc2b2de1
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Definitions.Def_MarkovProcess_V3H_Path_StoppingTimeDyadicCeiling_2d75c809
import Definitions.Def_MarkovProcess_V3H_Time_FiniteDenseApproximationOrdered_4fc0c4f5
import Definitions.Def_MarkovProcess_V3H_Trajectory_DenseRestrictionMarginals_931e4c17
import Definitions.Def_MarkovProcess_V3H_Trajectory_Equivariance_2a745e86
import Definitions.Def_MarkovProcess_V3H_Trajectory_FellerRestrictedRestart_8026f3b2
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

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Properties of the parameterized continuous-path process

Every property of the continuous-path process of a single semigroup, as exposed in
`MarkovProcess/Main.lean`, restated for the measurably parameterized process
`ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess P hP` at a point
`(theta, x)` of the parameter-and-state space.  The hypotheses are the fibrewise ones: fibrewise
conservativity `hP`, fibrewise Feller property `hFeller` where the single-semigroup statement needs
it, and fibrewise Kolmogorov regularity `hK`.

Every proof is a transport through the exact fibre identity
`IsConservative.continuousProcess_apply`; consumers never need that identity themselves.  The
restarted kernels are written as the parameterized kernel composed with the map
`omega ↦ (theta, omega (T omega))`, so that the parameter is carried along the restart.

Main statements: `continuousProcess_map_eval`, `continuousProcess_map_eval_zero` (and its kernel
form `continuousProcess_map_eval_zero'`), `continuousProcess_map_finiteEvaluation`,
`continuousProcess_map_finiteEvaluation_denseTime`, `continuousProcess_map_shift`,
`continuousProcess_restrict_map_shift`, `continuousProcess_restrict_map_shift_stoppingTime`,
`continuousProcess_condExp_shift`, `continuousProcess_condExp_shift_stoppingTime`,
`continuousProcess_condExp_shift_countableStoppingTime`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]



end ContinuousPath

namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)

section Fibre







end Fibre

section Marginals









variable [LocallyCompactSpace alpha]
  (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)

include hFeller









variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]







end Marginals

end ParameterizedSubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Properties of the parameterized continuous-path process

Every property of the continuous-path process of a single semigroup, as exposed in
`MarkovProcess/Main.lean`, restated for the measurably parameterized process
`ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess P hP` at a point
`(theta, x)` of the parameter-and-state space.  The hypotheses are the fibrewise ones: fibrewise
conservativity `hP`, fibrewise Feller property `hFeller` where the single-semigroup statement needs
it, and fibrewise Kolmogorov regularity `hK`.

Every proof is a transport through the exact fibre identity
`IsConservative.continuousProcess_apply`; consumers never need that identity themselves.  The
restarted kernels are written as the parameterized kernel composed with the map
`omega ↦ (theta, omega (T omega))`, so that the parameter is carried along the restart.

Main statements: `continuousProcess_map_eval`, `continuousProcess_map_eval_zero` (and its kernel
form `continuousProcess_map_eval_zero'`), `continuousProcess_map_finiteEvaluation`,
`continuousProcess_map_finiteEvaluation_denseTime`, `continuousProcess_map_shift`,
`continuousProcess_restrict_map_shift`, `continuousProcess_restrict_map_shift_stoppingTime`,
`continuousProcess_condExp_shift`, `continuousProcess_condExp_shift_stoppingTime`,
`continuousProcess_condExp_shift_countableStoppingTime`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal




variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)











variable [LocallyCompactSpace alpha]
  (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)

include hFeller



section AuxSecM
omit hFeller
variable {α₁ : Type*} [MetricSpace α₁] [CompleteSpace α₁]
  [MeasurableSpace α₁] [BorelSpace α₁] [SecondCountableTopology α₁]
  [Nonempty α₁] [LocallyCompactSpace α₁]
variable (P₁ : MarkovProcess.SubMarkovKernelSemigroup α₁) (hP₁ : P₁.IsConservative)
  (default : ContinuousPath α₁)
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
    (continuousPathTrajectory P₁ hP₁ default).map (ContinuousPath.finiteEvaluation (fun i ↦ times i)) =
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
    P₁ hP₁ default hK J
  have hb' : (continuousPathTrajectory P₁ hP₁ default).map (ContinuousPath.finsetEvaluation S) =
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
    (continuousPathTrajectory P₁ hP₁ default).map (ContinuousPath.finiteEvaluation (fun i ↦ times i)) =
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
      ∫ ω, f (ContinuousPath.finiteEvaluation (fun i => tk k i) ω) ∂(continuousPathTrajectory P₁ hP₁ default x) := by
    intro k
    rw [← AuxB_rational P₁ hP₁ default hK (tk k) (q k) (htk k), Kernel.map_apply _ (hEv _),
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
    (continuousPathTrajectory P₁ hP₁ default).map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P₁ I := by
  rw [AuxB_finsetEval_eq, Kernel.map_comp_right _
    (ContinuousPath.continuous_finiteEvaluation _).measurable
    (measurable_orderedPathToFiniteSet I), AuxB_ordered P₁ hP₁ default hFeller hK, finiteSetKernel_eq_map]


omit [LocallyCompactSpace α₁] in
include hP₁ in
theorem AuxS_ck (s : NNReal) : ∀ {n : ℕ} (τ : FiniteOrderedTimes n),
    finiteTimeKernel P₁ (OrderEmbedding.ofStrictMono (fun i => s + τ i)
      (fun a b h => add_lt_add_right (τ.strictMono h) s)) = (finiteTimeKernel P₁ τ).comp (P₁ s)
  | 0, τ => by
      haveI : IsMarkovKernel (P₁ s) := ⟨fun x => ⟨hP₁ s x⟩⟩
      rw [finiteTimeKernel_zero, finiteTimeKernel_zero, Kernel.const_comp']
  | n + 1, τ => by
      have hrel : FiniteOrderedTimes.relativeTail (OrderEmbedding.ofStrictMono (fun i => s + τ i)
          (fun a b h => add_lt_add_right (τ.strictMono h) s) : FiniteOrderedTimes (n + 1))
          = τ.relativeTail := by
        apply DFunLike.ext
        intro i
        simp only [FiniteOrderedTimes.relativeTail_apply, OrderEmbedding.coe_ofStrictMono]
        exact add_tsub_add_eq_tsub_left _ _ _
      haveI : IsMarkovKernel (finiteTimeKernel P₁ τ.relativeTail) :=
        IsConservative.isMarkovKernel_finiteTimeKernel _ hP₁ _
      haveI : IsFiniteKernel (P₁.kernel (τ 0)) := (P₁.isSubMarkovKernel _).isFiniteKernel
      haveI : IsFiniteKernel (P₁.kernel s) := (P₁.isSubMarkovKernel _).isFiniteKernel
      rw [finiteTimeKernel_succ, finiteTimeKernel_succ, hrel,
        Kernel.mapOfMeasurable_eq_map _ measurable_finCons,
        Kernel.mapOfMeasurable_eq_map _ measurable_finCons, ← Kernel.map_comp]
      congr 1
      change (P₁.kernel (s + τ 0) ⊗ₖ _) = _
      rw [P₁.kernel_add]
      ext x A hA
      rw [Kernel.compProd_apply hA, Kernel.comp_apply' _ _ _ hA]
      simp only [Kernel.prodMkLeft_apply]
      rw [Kernel.lintegral_comp _ _ _ (Kernel.measurable_kernel_prodMk_left hA)]
      refine lintegral_congr fun y => ?_
      rw [Kernel.compProd_apply hA]
      simp only [Kernel.prodMkLeft_apply]


theorem AuxM_shift
    (P₁ : SubMarkovKernelSemigroup α₁) (hFeller : P₁.IsFellerKernelSemigroup)
    (hP₁ : P₁.IsConservative) (default : ContinuousPath α₁)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P₁ hP₁ DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (s : NNReal) :
    (continuousPathTrajectory P₁ hP₁ default).map (ContinuousPath.shift s) =
      (continuousPathTrajectory P₁ hP₁ default).comp (P₁ s) := by
  have hsh : Measurable (ContinuousPath.shift s : ContinuousPath α₁ → ContinuousPath α₁) :=
    (ContinuousPath.continuous_shift_fixed s).measurable
  have hEv : ∀ I : Finset NNReal, Measurable (ContinuousPath.finsetEvaluation (alpha := α₁) I) :=
    fun I => (ContinuousPath.continuous_finiteEvaluation _).measurable
  haveI : IsMarkovKernel (P₁ s) := ⟨fun x => ⟨hP₁ s x⟩⟩
  haveI : IsMarkovKernel ((continuousPathTrajectory P₁ hP₁ default).map (ContinuousPath.shift s)) :=
    Kernel.IsMarkovKernel.map _ hsh
  have hQ : ∀ J : Finset DenseTime,
      ((continuousPathTrajectory P₁ hP₁ default).map (ContinuousPath.shift s)).map
          (ContinuousPath.finsetEvaluation (denseTimePhysicalSet J)) =
        ((continuousPathTrajectory P₁ hP₁ default).comp (P₁ s)).map
          (ContinuousPath.finsetEvaluation (denseTimePhysicalSet J)) := by
    intro J
    set S := denseTimePhysicalSet J
    set τ := finiteSetTimes S
    have hFE : Measurable (ContinuousPath.finiteEvaluation (α := α₁)
        (fun i ↦ (OrderEmbedding.ofStrictMono (fun i => s + τ i)
          (fun a b h => add_lt_add_right (τ.strictMono h) s) : FiniteOrderedTimes _) i)) :=
      (ContinuousPath.continuous_finiteEvaluation _).measurable
    have hfun : ContinuousPath.finsetEvaluation (alpha := α₁) S ∘ ContinuousPath.shift s =
        orderedPathToFiniteSet S ∘
          ContinuousPath.finiteEvaluation (fun i ↦ (OrderEmbedding.ofStrictMono (fun i => s + τ i)
            (fun a b h => add_lt_add_right (τ.strictMono h) s) : FiniteOrderedTimes _) i) := by
      funext path t
      simp only [Function.comp_apply, orderedPathToFiniteSet, ContinuousPath.finiteEvaluation,
        ContinuousPath.finsetEvaluation, OrderEmbedding.coe_ofStrictMono, ContinuousPath.shift_apply, τ,
        finiteSetTimes]
      rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
    rw [← Kernel.map_comp_right _ hsh (hEv S), hfun,
      Kernel.map_comp_right _ hFE (measurable_orderedPathToFiniteSet S),
      AuxB_ordered P₁ hP₁ default hFeller hK, AuxS_ck P₁ hP₁ s τ, Kernel.map_comp, Kernel.map_comp,
      AuxB_finset P₁ hP₁ default hFeller hK, finiteSetKernel_eq_map]
  have key : ∀ (I : Finset DenseTime) (R : Kernel α₁ (ContinuousPath α₁)),
      (R.map ContinuousPath.denseRestriction).map I.restrict =
        (R.map (ContinuousPath.finsetEvaluation (denseTimePhysicalSet I))).map
          (DenseTimePath.pullbackPhysicalSet I) := by
    intro I R
    have hfun : I.restrict ∘ ContinuousPath.denseRestriction =
        DenseTimePath.pullbackPhysicalSet I ∘
          ContinuousPath.finsetEvaluation (alpha := α₁) (denseTimePhysicalSet I) := by
      funext path
      exact (DenseTimePath.pullbackPhysicalSet_evaluation I path).symm
    rw [← Kernel.map_comp_right _ ContinuousPath.measurable_denseRestriction
      (Finset.measurable_restrict I), hfun,
      Kernel.map_comp_right _ (hEv _) (DenseTimePath.measurable_pullbackPhysicalSet I)]
  have hd : ((continuousPathTrajectory P₁ hP₁ default).map (ContinuousPath.shift s)).map
        ContinuousPath.denseRestriction =
      ((continuousPathTrajectory P₁ hP₁ default).comp (P₁ s)).map ContinuousPath.denseRestriction := by
    apply Kernel.p2m_embedded_cf5a87fc6ca47934
    intro I
    rw [key, key, hQ]
  have hemb := ContinuousPath.measurableEmbedding_denseRestriction (alpha := α₁)
  ext x A hA
  have h1 := congrArg (fun R => R x (ContinuousPath.denseRestriction '' A)) hd
  simp only [Kernel.map_apply _ ContinuousPath.measurable_denseRestriction] at h1
  rw [hemb.map_apply, hemb.map_apply, hemb.injective.preimage_image] at h1
  exact h1

end AuxSecM

open MarkovProcess.ParameterizedSubMarkovKernelSemigroup in
theorem solution (hK : P.KolmogorovRegular hP)
    (theta : Theta) (x : alpha) (s : NNReal) :
    (IsConservative.continuousProcess P hP (theta, x)).map (ContinuousPath.shift s) =
      ((P.toSubMarkovKernelSemigroup theta) s x).bind
        (fun y ↦ IsConservative.continuousProcess P hP (theta, y)) := by
  have hsh : Measurable (ContinuousPath.shift s : ContinuousPath alpha → ContinuousPath alpha) :=
    (ContinuousPath.continuous_shift_fixed s).measurable
  simp_rw [IsConservative.continuousProcess_apply]
  have h1 := AuxM_shift (P.toSubMarkovKernelSemigroup theta) (hFeller theta) (hP theta)
    (ContinuousMap.const NNReal (Classical.arbitrary alpha)) (hK theta) s
  have h2 := DFunLike.congr_fun h1 x
  rw [Kernel.map_apply _ hsh, Kernel.comp_apply] at h2
  exact h2
