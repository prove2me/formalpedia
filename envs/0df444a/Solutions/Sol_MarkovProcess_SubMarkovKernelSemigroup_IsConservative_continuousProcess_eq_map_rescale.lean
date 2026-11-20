-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousProcess_eq_map_rescale
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:49:56.212661+00:00
-- url     : https://prove2.me/submissions/cdd1d991-70de-40d0-80b6-aa49b801152d

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

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Equivariance of the continuous-path process

Let `P` be a conservative Feller sub-Markov kernel semigroup on `alpha` with a Kolmogorov-regular
continuous-path process, let `e : alpha ≃ₜ beta` be a homeomorphism onto a second state space and
`c > 0` a time factor, and let `P'` be the rescaled conjugate of `P` on `beta`, that is
`P' t x = ((P (c * t)) (e.symm x)).map e`.  Then the continuous-path process of `P'` is the
continuous-path process of `P` started at `e.symm x` and pushed forward by the path map
`omega ↦ fun t ↦ e (omega (c * t))`.

The proof goes through the uniqueness theorem of `MarkovProcess/Main.lean`: the pushed-forward
kernel is a Markov kernel whose finite-dimensional distributions are computed from the Feller
marginal theorem for `P` at the rescaled times together with the finite-dimensional transfer
`SubMarkovKernelSemigroup.IsRescaledConjugate.finiteSetKernel_eq`.

Main results: `ContinuousPath.rescale` and its continuity and measurability;
`SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation_ordered`,
the marginal of the continuous-path process at an arbitrary strictly increasing finite family of
times; `SubMarkovKernelSemigroup.IsConservative.continuousProcess_eq_map_rescale` and its
pointwise form `continuousProcess_apply_rescale`; the intrinsic form
`continuousProcess_eq_map_rescale_of_hasKolmogorovMoments`, whose only regularity hypothesis is a
Kolmogorov moment bound on `P` when `e` is an isometry; and the two degenerate corollaries, pure
time rescaling (`continuousProcess_eq_map_timeRescale`) and pure conjugation
(`continuousProcess_eq_map_conjugate`).

No scaling limit is asserted: `c` is a fixed positive factor and both semigroups are given in
advance.  The two state spaces may coincide; the degenerate corollaries are stated on one space.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

namespace ContinuousPath

section Rescale

variable {alpha beta gamma : Type*} [TopologicalSpace alpha] [TopologicalSpace beta]
  [TopologicalSpace gamma]























end Rescale

end ContinuousPath

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



section TwoSpaces

variable {beta : Type*} [MetricSpace beta] [CompleteSpace beta]
  [MeasurableSpace beta] [BorelSpace beta] [SecondCountableTopology beta] [Nonempty beta]

variable (P' : SubMarkovKernelSemigroup beta) (hP' : P'.IsConservative)







end TwoSpaces

section OneSpace

variable (P' : SubMarkovKernelSemigroup alpha) (hP' : P'.IsConservative)





end OneSpace

end

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
# Equivariance of the continuous-path process

Let `P` be a conservative Feller sub-Markov kernel semigroup on `alpha` with a Kolmogorov-regular
continuous-path process, let `e : alpha ≃ₜ beta` be a homeomorphism onto a second state space and
`c > 0` a time factor, and let `P'` be the rescaled conjugate of `P` on `beta`, that is
`P' t x = ((P (c * t)) (e.symm x)).map e`.  Then the continuous-path process of `P'` is the
continuous-path process of `P` started at `e.symm x` and pushed forward by the path map
`omega ↦ fun t ↦ e (omega (c * t))`.

The proof goes through the uniqueness theorem of `MarkovProcess/Main.lean`: the pushed-forward
kernel is a Markov kernel whose finite-dimensional distributions are computed from the Feller
marginal theorem for `P` at the rescaled times together with the finite-dimensional transfer
`SubMarkovKernelSemigroup.IsRescaledConjugate.finiteSetKernel_eq`.

Main results: `ContinuousPath.rescale` and its continuity and measurability;
`SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation_ordered`,
the marginal of the continuous-path process at an arbitrary strictly increasing finite family of
times; `SubMarkovKernelSemigroup.IsConservative.continuousProcess_eq_map_rescale` and its
pointwise form `continuousProcess_apply_rescale`; the intrinsic form
`continuousProcess_eq_map_rescale_of_hasKolmogorovMoments`, whose only regularity hypothesis is a
Kolmogorov moment bound on `P` when `e` is an isometry; and the two degenerate corollaries, pure
time rescaling (`continuousProcess_eq_map_timeRescale`) and pure conjugation
(`continuousProcess_eq_map_conjugate`).

No scaling limit is asserted: `c` is a fixed positive factor and both semigroups are given in
advance.  The two state spaces may coincide; the degenerate corollaries are stated on one space.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal





open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)




variable {beta : Type*} [MetricSpace beta] [CompleteSpace beta]
  [MeasurableSpace beta] [BorelSpace beta] [SecondCountableTopology beta] [Nonempty beta]

variable (P' : SubMarkovKernelSemigroup beta) (hP' : P'.IsConservative)


open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup

omit [LocallyCompactSpace alpha] in
include hP hP' in
theorem AuxC_ftk {e : alpha ≃ₜ beta} {c : NNReal} (hc : 0 < c) (h : IsRescaledConjugate P P' e c) :
    ∀ {n : ℕ} (times : FiniteOrderedTimes n) (x : beta),
      finiteTimeKernel P' times x =
        (finiteTimeKernel P (times.rescale c hc) (e.symm x)).map (fun p i => e (p i))
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
      have hme : ∀ m : ℕ, Measurable (fun (p : Fin m → alpha) (i : Fin m) => e (p i)) := by
        intro m
        exact measurable_pi_lambda _ fun i => e.continuous.measurable.comp (measurable_pi_apply i)
      haveI : IsMarkovKernel (finiteTimeKernel P' times.relativeTail) :=
        IsConservative.isMarkovKernel_finiteTimeKernel _ hP' _
      haveI : IsMarkovKernel (finiteTimeKernel P (times.rescale c hc).relativeTail) :=
        IsConservative.isMarkovKernel_finiteTimeKernel _ hP _
      haveI : IsFiniteKernel (P'.kernel (times 0)) :=
        (P'.isSubMarkovKernel (times 0)).isFiniteKernel
      haveI : IsFiniteKernel (P.kernel ((times.rescale c hc) 0)) :=
        (P.isSubMarkovKernel _).isFiniteKernel
      ext s hs
      rw [finiteTimeKernel_succ, finiteTimeKernel_succ,
        Kernel.mapOfMeasurable_eq_map _ measurable_finCons,
        Kernel.mapOfMeasurable_eq_map _ measurable_finCons,
        Kernel.map_apply _ measurable_finCons, Kernel.map_apply _ measurable_finCons,
        Measure.map_apply (hme _) hs, Measure.map_apply measurable_finCons hs,
        Measure.map_apply measurable_finCons ((hme _) hs),
        Kernel.compProd_apply (measurable_finCons hs),
        Kernel.compProd_apply (measurable_finCons ((hme _) hs))]
      change ∫⁻ b, _ ∂(P' (times 0) x) = ∫⁻ b, _ ∂(P (c * times 0) (e.symm x))
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

open MarkovProcess.SubMarkovKernelSemigroup in
theorem solution
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (hK' : P'.KolmogorovRegular hP') {e : alpha ≃ₜ beta} {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P' e c) :
    continuousProcess P' hP' =
      (Kernel.comap (continuousProcess P hP) e.symm e.symm.measurable).map
        (ContinuousPath.rescale e c) := by
  have hresc : Measurable (ContinuousPath.rescale e c) := by
    have : Continuous (ContinuousPath.rescale e c) :=
      (ContinuousMap.continuous_postcomp _).comp (ContinuousMap.continuous_precomp _)
    exact this.measurable
  have hEv : ∀ I : Finset NNReal, Measurable (ContinuousPath.finsetEvaluation (alpha := beta) I) :=
    fun I => (ContinuousPath.continuous_finiteEvaluation _).measurable
  have hme : ∀ m : ℕ, Measurable (fun (p : Fin m → alpha) (i : Fin m) => e (p i)) := by
    intro m
    exact measurable_pi_lambda _ fun i => e.continuous.measurable.comp (measurable_pi_apply i)
  set Q := (Kernel.comap (continuousProcess P hP) e.symm e.symm.measurable).map
    (ContinuousPath.rescale e c) with hQdef
  have hQ : ∀ J : Finset DenseTime, Q.map (ContinuousPath.finsetEvaluation (denseTimePhysicalSet J)) =
      finiteSetKernel P' (denseTimePhysicalSet J) := by
    intro J
    set S := denseTimePhysicalSet J
    have hFE : Measurable (ContinuousPath.finiteEvaluation (α := alpha)
        (fun i ↦ (finiteSetTimes S).rescale c hc i)) :=
      (ContinuousPath.continuous_finiteEvaluation _).measurable
    have h1 : Measurable (orderedPathToFiniteSet S ∘ (fun (p : Fin S.card → alpha) i => e (p i))) :=
      (measurable_orderedPathToFiniteSet S).comp (hme _)
    have hfun : ContinuousPath.finsetEvaluation (alpha := beta) S ∘ ContinuousPath.rescale e c =
        (orderedPathToFiniteSet S ∘ (fun (p : Fin S.card → alpha) i => e (p i))) ∘
          ContinuousPath.finiteEvaluation (fun i ↦ (finiteSetTimes S).rescale c hc i) := by
      funext path t
      simp only [Function.comp_apply, orderedPathToFiniteSet, ContinuousPath.finiteEvaluation,
        finiteSetTimes, FiniteOrderedTimes.rescale, OrderEmbedding.coe_ofStrictMono]
      rw [ContinuousPath.p2m_embedded_f5285285254f4af5, ← Finset.coe_orderIsoOfFin_apply,
        OrderIso.apply_symm_apply]
    ext x : 1
    rw [hQdef, Kernel.map_apply _ (hEv S), Kernel.map_apply _ hresc, Kernel.comap_apply,
      Measure.map_map (hEv S) hresc, hfun, ← Measure.map_map h1 hFE, ← Kernel.map_apply _ hFE,
      AuxB_ordered P hP hFeller hK, finiteSetKernel_eq_map,
      Kernel.map_apply _ (measurable_orderedPathToFiniteSet S), AuxC_ftk P hP P' hP' hc h,
      Measure.map_map (measurable_orderedPathToFiniteSet S) (hme _)]
  have hmarg : ∀ J : Finset DenseTime,
      (continuousProcess P' hP').map (ContinuousPath.finsetEvaluation (denseTimePhysicalSet J)) =
        finiteSetKernel P' (denseTimePhysicalSet J) :=
    fun J => _root_.MarkovProcess.SubMarkovKernelSemigroup.IsConservative.p2m_embedded_b819d8df72e216cf
      P' hP' (ContinuousMap.const NNReal (Classical.arbitrary beta)) hK' J
  have key : ∀ (I : Finset DenseTime) (R : Kernel beta (ContinuousPath beta)),
      (R.map ContinuousPath.denseRestriction).map I.restrict =
        (R.map (ContinuousPath.finsetEvaluation (denseTimePhysicalSet I))).map
          (DenseTimePath.pullbackPhysicalSet I) := by
    intro I R
    have hfun : I.restrict ∘ ContinuousPath.denseRestriction =
        DenseTimePath.pullbackPhysicalSet I ∘
          ContinuousPath.finsetEvaluation (alpha := beta) (denseTimePhysicalSet I) := by
      funext path
      exact (DenseTimePath.pullbackPhysicalSet_evaluation I path).symm
    rw [← Kernel.map_comp_right _ ContinuousPath.measurable_denseRestriction
      (Finset.measurable_restrict I), hfun,
      Kernel.map_comp_right _ (hEv _) (DenseTimePath.measurable_pullbackPhysicalSet I)]
  have hd : (continuousProcess P' hP').map ContinuousPath.denseRestriction =
      Q.map ContinuousPath.denseRestriction := by
    apply Kernel.p2m_embedded_cf5a87fc6ca47934
    intro I
    rw [key, key, hQ, hmarg]
  have hemb := ContinuousPath.measurableEmbedding_denseRestriction (alpha := beta)
  ext x s hs
  have h1 := congrArg (fun R => R x (ContinuousPath.denseRestriction '' s)) hd
  simp only [Kernel.map_apply _ ContinuousPath.measurable_denseRestriction] at h1
  rw [hemb.map_apply, hemb.map_apply, hemb.injective.preimage_image] at h1
  exact h1
