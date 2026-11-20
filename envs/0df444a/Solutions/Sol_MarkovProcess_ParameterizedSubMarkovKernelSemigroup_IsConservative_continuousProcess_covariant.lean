-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_covariant
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:53:47.288295+00:00
-- url     : https://prove2.me/submissions/82007c27-ad6c-4be7-b05e-14325903613b

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
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelEquivariance_10113825
import Definitions.Def_MarkovProcess_V3H_Trajectory_Equivariance_2a745e86
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcess_caf2584d
import Definitions.Def_MarkovProcess_V3H_Parameterized_Equivariance_252d78e3
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

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Equivariance of the parameterized continuous-path process

The equivariance theorem of `MarkovProcess/Trajectory/Equivariance.lean`, restated for a measurably
parameterized family of sub-Markov kernel semigroups.  Here the state map `e` and the time factor
`c` are accompanied by a measurable reparameterization `g` of the parameter space, and the
intertwining hypothesis is fibrewise:
`P' theta t x = ((P (g theta) (c * t)) (e.symm x)).map e`.

The conclusion is a single identity of kernels on `Theta × alpha`: the quenched continuous-path
process of `P'` is the quenched process of `P` pulled back along `(theta, x) ↦ (g theta, e.symm x)`
and pushed forward by `ContinuousPath.rescale e c`.  The proof is fibrewise, through the exact
fibre identity `IsConservative.continuousProcess_apply`.

Main results: `ParameterizedSubMarkovKernelSemigroup.IsRescaledConjugate` with its fibre form and
its transfers of conservativity and of the Kolmogorov moment criterion;
`IsConservative.continuousProcess_eq_map_rescale`, its pointwise form and its intrinsic form
`continuousProcess_eq_map_rescale_of_hasKolmogorovMoments`; the covariance corollary
`IsConservative.continuousProcess_covariant` for a family that is its own rescaled conjugate, of
which stationarity and re-gauging covariance of a random environment (`g` the environment shift,
`e` the spatial translation, `c = 1`) are instances.

No scaling limit and no ergodic statement is asserted: the environment map `g`, the factor `c`
and both families are given in advance, and nothing is claimed about the law of the environment.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

section Measurability

variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [TopologicalSpace beta] [MeasurableSpace beta]
  [BorelSpace beta]





namespace IsRescaledConjugate

variable {P : ParameterizedSubMarkovKernelSemigroup Theta alpha}
  {P' : ParameterizedSubMarkovKernelSemigroup Theta beta} {g : Theta → Theta}
  {e : alpha ≃ₜ beta} {c : NNReal}





end IsRescaledConjugate

end Measurability

section Moments

variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [PseudoEMetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [PseudoEMetricSpace beta] [MeasurableSpace beta]
  [BorelSpace beta]
variable {P : ParameterizedSubMarkovKernelSemigroup Theta alpha}
  {P' : ParameterizedSubMarkovKernelSemigroup Theta beta} {g : Theta → Theta}
  {e : alpha ≃ₜ beta} {c : NNReal}



end Moments

section ContinuousProcess

variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [MetricSpace alpha]
  [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha] [MetricSpace beta] [CompleteSpace beta]
  [MeasurableSpace beta] [BorelSpace beta] [SecondCountableTopology beta] [Nonempty beta]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
  (P' : ParameterizedSubMarkovKernelSemigroup Theta beta)
  (hP : P.IsConservative) (hP' : P'.IsConservative)









end ContinuousProcess

end

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
# Equivariance of the parameterized continuous-path process

The equivariance theorem of `MarkovProcess/Trajectory/Equivariance.lean`, restated for a measurably
parameterized family of sub-Markov kernel semigroups.  Here the state map `e` and the time factor
`c` are accompanied by a measurable reparameterization `g` of the parameter space, and the
intertwining hypothesis is fibrewise:
`P' theta t x = ((P (g theta) (c * t)) (e.symm x)).map e`.

The conclusion is a single identity of kernels on `Theta × alpha`: the quenched continuous-path
process of `P'` is the quenched process of `P` pulled back along `(theta, x) ↦ (g theta, e.symm x)`
and pushed forward by `ContinuousPath.rescale e c`.  The proof is fibrewise, through the exact
fibre identity `IsConservative.continuousProcess_apply`.

Main results: `ParameterizedSubMarkovKernelSemigroup.IsRescaledConjugate` with its fibre form and
its transfers of conservativity and of the Kolmogorov moment criterion;
`IsConservative.continuousProcess_eq_map_rescale`, its pointwise form and its intrinsic form
`continuousProcess_eq_map_rescale_of_hasKolmogorovMoments`; the covariance corollary
`IsConservative.continuousProcess_covariant` for a family that is its own rescaled conjugate, of
which stationarity and re-gauging covariance of a random environment (`g` the environment shift,
`e` the spatial translation, `c = 1`) are instances.

No scaling limit and no ergodic statement is asserted: the environment map `g`, the factor `c`
and both families are given in advance, and nothing is claimed about the law of the environment.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal






variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [MetricSpace alpha]
  [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha] [MetricSpace beta] [CompleteSpace beta]
  [MeasurableSpace beta] [BorelSpace beta] [SecondCountableTopology beta] [Nonempty beta]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
  (P' : ParameterizedSubMarkovKernelSemigroup Theta beta)
  (hP : P.IsConservative) (hP' : P'.IsConservative)








section AuxSec2
variable {α₁ : Type*} [MetricSpace α₁] [CompleteSpace α₁]
  [MeasurableSpace α₁] [BorelSpace α₁] [SecondCountableTopology α₁]
  [Nonempty α₁] [LocallyCompactSpace α₁]
variable (P₁ : MarkovProcess.SubMarkovKernelSemigroup α₁) (hP₁ : P₁.IsConservative)
variable {β₁ : Type*} [MetricSpace β₁] [CompleteSpace β₁]
  [MeasurableSpace β₁] [BorelSpace β₁] [SecondCountableTopology β₁] [Nonempty β₁]
variable (P₂ : MarkovProcess.SubMarkovKernelSemigroup β₁) (hP₂ : P₂.IsConservative)
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative

open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup

omit [LocallyCompactSpace α₁] in
include hP₁ hP₂ in
theorem AuxC_ftk {e : α₁ ≃ₜ β₁} {c : NNReal} (hc : 0 < c) (h : IsRescaledConjugate P₁ P₂ e c) :
    ∀ {n : ℕ} (times : FiniteOrderedTimes n) (x : β₁),
      finiteTimeKernel P₂ times x =
        (finiteTimeKernel P₁ (times.rescale c hc) (e.symm x)).map (fun p i => e (p i))
  | 0, times, x => by
      rw [finiteTimeKernel_zero, finiteTimeKernel_zero, Kernel.const_apply, Kernel.const_apply,
        Measure.map_dirac' (by fun_prop)]
      congr 1
      funext i
      exact i.elim0
  | n + 1, times, x => by
      have hrel : (times.rescale c hc).relativeTail = times.relativeTail.rescale c hc := by
        apply DFunLike.ext
        intro i
        simp only [FiniteOrderedTimes.relativeTail_apply, FiniteOrderedTimes.rescale,
          OrderEmbedding.coe_ofStrictMono, mul_tsub]
        rfl
      have hme : ∀ m : ℕ, Measurable (fun (p : Fin m → α₁) (i : Fin m) => e (p i)) := by
        intro m
        exact measurable_pi_lambda _ fun i => e.continuous.measurable.comp (measurable_pi_apply i)
      haveI : IsMarkovKernel (finiteTimeKernel P₂ times.relativeTail) :=
        IsConservative.isMarkovKernel_finiteTimeKernel _ hP₂ _
      haveI : IsMarkovKernel (finiteTimeKernel P₁ (times.rescale c hc).relativeTail) :=
        IsConservative.isMarkovKernel_finiteTimeKernel _ hP₁ _
      haveI : IsFiniteKernel (P₂.kernel (times 0)) :=
        (P₂.isSubMarkovKernel (times 0)).isFiniteKernel
      haveI : IsFiniteKernel (P₁.kernel ((times.rescale c hc) 0)) :=
        (P₁.isSubMarkovKernel _).isFiniteKernel
      ext s hs
      rw [finiteTimeKernel_succ, finiteTimeKernel_succ,
        Kernel.mapOfMeasurable_eq_map _ measurable_finCons,
        Kernel.mapOfMeasurable_eq_map _ measurable_finCons,
        Kernel.map_apply _ measurable_finCons, Kernel.map_apply _ measurable_finCons,
        Measure.map_apply (hme _) hs, Measure.map_apply measurable_finCons hs,
        Measure.map_apply measurable_finCons ((hme _) hs),
        Kernel.compProd_apply (measurable_finCons hs),
        Kernel.compProd_apply (measurable_finCons ((hme _) hs))]
      change ∫⁻ b, _ ∂(P₂ (times 0) x) = ∫⁻ b, _ ∂(P₁ (c * times 0) (e.symm x))
      simp only [Kernel.prodMkLeft_apply]
      rw [h, lintegral_map (Kernel.measurable_kernel_prodMk_left (measurable_finCons hs))
        e.continuous.measurable]
      refine lintegral_congr fun z => ?_
      rw [AuxC_ftk hc h times.relativeTail, Homeomorph.symm_apply_apply, hrel,
        Measure.map_apply (hme _) (measurable_prodMk_left (measurable_finCons hs))]
      congr 1
      ext p
      simp only [Set.mem_preimage]
      constructor <;> intro hp <;> convert hp using 2 <;> rename_i i <;>
        refine Fin.cases ?_ (fun j => ?_) i <;> simp


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

open MarkovProcess.SubMarkovKernelSemigroup in
theorem AuxR_main
    (hFeller : P₁.IsFellerKernelSemigroup) (hK : P₁.KolmogorovRegular hP₁)
    (hK' : P₂.KolmogorovRegular hP₂) {e : α₁ ≃ₜ β₁} {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P₁ P₂ e c) :
    continuousProcess P₂ hP₂ =
      (Kernel.comap (continuousProcess P₁ hP₁) e.symm e.symm.measurable).map
        (ContinuousPath.rescale e c) := by
  have hresc : Measurable (ContinuousPath.rescale e c) := by
    have : Continuous (ContinuousPath.rescale e c) :=
      (ContinuousMap.continuous_postcomp _).comp (ContinuousMap.continuous_precomp _)
    exact this.measurable
  have hEv : ∀ I : Finset NNReal, Measurable (ContinuousPath.finsetEvaluation (alpha := β₁) I) :=
    fun I => (ContinuousPath.continuous_finiteEvaluation _).measurable
  have hme : ∀ m : ℕ, Measurable (fun (p : Fin m → α₁) (i : Fin m) => e (p i)) := by
    intro m
    exact measurable_pi_lambda _ fun i => e.continuous.measurable.comp (measurable_pi_apply i)
  set Q := (Kernel.comap (continuousProcess P₁ hP₁) e.symm e.symm.measurable).map
    (ContinuousPath.rescale e c) with hQdef
  have hQ : ∀ J : Finset DenseTime, Q.map (ContinuousPath.finsetEvaluation (denseTimePhysicalSet J)) =
      finiteSetKernel P₂ (denseTimePhysicalSet J) := by
    intro J
    set S := denseTimePhysicalSet J
    have hFE : Measurable (ContinuousPath.finiteEvaluation (α := α₁)
        (fun i ↦ (finiteSetTimes S).rescale c hc i)) :=
      (ContinuousPath.continuous_finiteEvaluation _).measurable
    have h1 : Measurable (orderedPathToFiniteSet S ∘ (fun (p : Fin S.card → α₁) i => e (p i))) :=
      (measurable_orderedPathToFiniteSet S).comp (hme _)
    have hfun : ContinuousPath.finsetEvaluation (alpha := β₁) S ∘ ContinuousPath.rescale e c =
        (orderedPathToFiniteSet S ∘ (fun (p : Fin S.card → α₁) i => e (p i))) ∘
          ContinuousPath.finiteEvaluation (fun i ↦ (finiteSetTimes S).rescale c hc i) := by
      funext path t
      simp only [Function.comp_apply, orderedPathToFiniteSet, ContinuousPath.finiteEvaluation,
        finiteSetTimes, FiniteOrderedTimes.rescale, OrderEmbedding.coe_ofStrictMono]
      rw [ContinuousPath.p2m_embedded_f5285285254f4af5, ← Finset.coe_orderIsoOfFin_apply,
        OrderIso.apply_symm_apply]
    ext x : 1
    rw [hQdef, Kernel.map_apply _ (hEv S), Kernel.map_apply _ hresc, Kernel.comap_apply,
      Measure.map_map (hEv S) hresc, hfun, ← Measure.map_map h1 hFE, ← Kernel.map_apply _ hFE,
      AuxB_ordered P₁ hP₁ hFeller hK, finiteSetKernel_eq_map,
      Kernel.map_apply _ (measurable_orderedPathToFiniteSet S), AuxC_ftk P₁ hP₁ P₂ hP₂ hc h,
      Measure.map_map (measurable_orderedPathToFiniteSet S) (hme _)]
  have hmarg : ∀ J : Finset DenseTime,
      (continuousProcess P₂ hP₂).map (ContinuousPath.finsetEvaluation (denseTimePhysicalSet J)) =
        finiteSetKernel P₂ (denseTimePhysicalSet J) :=
    fun J => _root_.MarkovProcess.SubMarkovKernelSemigroup.IsConservative.p2m_embedded_b819d8df72e216cf
      P₂ hP₂ (ContinuousMap.const NNReal (Classical.arbitrary β₁)) hK' J
  have key : ∀ (I : Finset DenseTime) (R : Kernel β₁ (ContinuousPath β₁)),
      (R.map ContinuousPath.denseRestriction).map I.restrict =
        (R.map (ContinuousPath.finsetEvaluation (denseTimePhysicalSet I))).map
          (DenseTimePath.pullbackPhysicalSet I) := by
    intro I R
    have hfun : I.restrict ∘ ContinuousPath.denseRestriction =
        DenseTimePath.pullbackPhysicalSet I ∘
          ContinuousPath.finsetEvaluation (alpha := β₁) (denseTimePhysicalSet I) := by
      funext path
      exact (DenseTimePath.pullbackPhysicalSet_evaluation I path).symm
    rw [← Kernel.map_comp_right _ ContinuousPath.measurable_denseRestriction
      (Finset.measurable_restrict I), hfun,
      Kernel.map_comp_right _ (hEv _) (DenseTimePath.measurable_pullbackPhysicalSet I)]
  have hd : (continuousProcess P₂ hP₂).map ContinuousPath.denseRestriction =
      Q.map ContinuousPath.denseRestriction := by
    apply Kernel.p2m_embedded_cf5a87fc6ca47934
    intro I
    rw [key, key, hQ, hmarg]
  have hemb := ContinuousPath.measurableEmbedding_denseRestriction (alpha := β₁)
  ext x s hs
  have h1 := congrArg (fun R => R x (ContinuousPath.denseRestriction '' s)) hd
  simp only [Kernel.map_apply _ ContinuousPath.measurable_denseRestriction] at h1
  rw [hemb.map_apply, hemb.map_apply, hemb.injective.preimage_image] at h1
  exact h1

end AuxSec2

open MarkovProcess.ParameterizedSubMarkovKernelSemigroup in
theorem AuxPar
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (hK' : P'.KolmogorovRegular hP')
    {g : Theta → Theta} {e : alpha ≃ₜ beta} {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P' g e c) (theta : Theta) (x : beta) :
    IsConservative.continuousProcess P' hP' (theta, x) =
      (IsConservative.continuousProcess P hP (g theta, e.symm x)).map
        (ContinuousPath.rescale e c) := by
  have hresc : Measurable (ContinuousPath.rescale e c) := by
    have : Continuous (ContinuousPath.rescale e c) :=
      (ContinuousMap.continuous_postcomp _).comp (ContinuousMap.continuous_precomp _)
    exact this.measurable
  rw [IsConservative.continuousProcess_apply, IsConservative.continuousProcess_apply]
  have hm := AuxR_main (P.toSubMarkovKernelSemigroup (g theta)) (hP (g theta))
    (P'.toSubMarkovKernelSemigroup theta) (hP' theta) (hFeller (g theta)) (hK (g theta))
    (hK' theta) hc (fun t y => h theta t y)
  rw [hm, Kernel.map_apply _ hresc, Kernel.comap_apply]

open MarkovProcess.ParameterizedSubMarkovKernelSemigroup in
theorem solution
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP)
    {g : Theta → Theta} (hg : Measurable g) {e : alpha ≃ₜ alpha} {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P g e c) :
    IsConservative.continuousProcess P hP =
      (Kernel.comap (IsConservative.continuousProcess P hP)
          (fun p : Theta × alpha ↦ (g p.1, e.symm p.2))
          (measurable_reparameterize hg e)).map (ContinuousPath.rescale e c) := by
  have hresc : Measurable (ContinuousPath.rescale e c) := by
    have : Continuous (ContinuousPath.rescale e c) :=
      (ContinuousMap.continuous_postcomp _).comp (ContinuousMap.continuous_precomp _)
    exact this.measurable
  ext ⟨theta, x⟩ : 1
  rw [Kernel.map_apply _ hresc, Kernel.comap_apply]
  exact AuxPar P P hP hP hFeller hK hK hc h theta x
