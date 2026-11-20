-- Prove2me | solution 1 for MarkovProcess.existsUnique_continuousProcess_driftSemigroup
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:36:35.341788+00:00
-- url     : https://prove2.me/submissions/ec71e996-0cd0-42f9-95b9-a81603039a5b

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
import Definitions.Def_MarkovProcess_V3H_Examples_Drift_f1e2d4e2
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
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
# The deterministic drift semigroup and its continuous-path process

On a finite-dimensional real normed space the transition semigroup that translates by `t • v` in
time `t` is a conservative Feller semigroup satisfying the Kolmogorov moment criterion with
exponents `p = q = 2` and constant `‖v‖²`.  The existence-and-uniqueness theorem of
`MarkovProcess.Main` therefore applies, and the process it produces is identified: from every
starting point `x` its law is the Dirac mass at the straight line `t ↦ x + t • v`.

Together with `MarkovProcess.Examples.Identity` this shows that the hypotheses of the main
theorem are satisfiable by a semigroup that genuinely moves.  Nothing here is claimed about a
semigroup with a nonzero diffusion part; for that see `MarkovProcess.Examples.HeatSemigroup`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Definition









end Definition

section Feller











end Feller

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
# The deterministic drift semigroup and its continuous-path process

On a finite-dimensional real normed space the transition semigroup that translates by `t • v` in
time `t` is a conservative Feller semigroup satisfying the Kolmogorov moment criterion with
exponents `p = q = 2` and constant `‖v‖²`.  The existence-and-uniqueness theorem of
`MarkovProcess.Main` therefore applies, and the process it produces is identified: from every
starting point `x` its law is the Dirac mass at the straight line `t ↦ x + t • v`.

Together with `MarkovProcess.Examples.Identity` this shows that the hypotheses of the main
theorem are satisfiable by a semigroup that genuinely moves.  Nothing here is claimed about a
semigroup with a nonzero diffusion part; for that see `MarkovProcess.Examples.HeatSemigroup`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]







open MarkovProcess in

theorem AuxDr_finiteTimeKernel (v : E) : ∀ {n : ℕ} (times : FiniteOrderedTimes n)
    (x : E),
    SubMarkovKernelSemigroup.finiteTimeKernel (driftSemigroup v) times x =
      Measure.dirac (fun i => x + (times i : ℝ) • v)
  | 0, times, x => by
      rw [SubMarkovKernelSemigroup.finiteTimeKernel_zero, Kernel.const_apply]
      congr 1
      funext i
      exact i.elim0
  | n + 1, times, x => by
      rw [SubMarkovKernelSemigroup.finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map _ MarkovProcess.measurable_finCons, Kernel.map_apply _ MarkovProcess.measurable_finCons]
      have hcp : ((driftSemigroup v) (times 0) ⊗ₖ
          Kernel.prodMkLeft E (SubMarkovKernelSemigroup.finiteTimeKernel
            (driftSemigroup v) times.relativeTail)) x =
          Measure.dirac (x + (times 0 : ℝ) • v,
            fun j : Fin n => (x + (times 0 : ℝ) • v) + (times.relativeTail j : ℝ) • v) := by
        haveI : IsMarkovKernel (SubMarkovKernelSemigroup.finiteTimeKernel
            (driftSemigroup v) times.relativeTail) :=
          SubMarkovKernelSemigroup.IsConservative.isMarkovKernel_finiteTimeKernel _
            (isConservative_driftSemigroup v) _
        haveI : IsSFiniteKernel ((driftSemigroup v).kernel (times 0)) := by
          change IsSFiniteKernel (Kernel.deterministic _ (measurable_driftTranslate v (times 0)))
          infer_instance
        ext s hs
        rw [Kernel.compProd_apply hs, driftSemigroup_apply, lintegral_dirac,
          Kernel.prodMkLeft_apply, AuxDr_finiteTimeKernel, Measure.dirac_apply' _ (measurable_prodMk_left hs),
          Measure.dirac_apply' _ hs]
        rfl
      rw [hcp, Measure.map_dirac' MarkovProcess.measurable_finCons]
      congr 1
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp only [Fin.cons_succ, FiniteOrderedTimes.relativeTail_apply]
        rw [NNReal.coe_sub (times.monotone (Fin.zero_le _)), sub_smul]
        abel

theorem solution (v : E) :
    ∃! Q : Kernel E (ContinuousPath E), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) =
          SubMarkovKernelSemigroup.finiteSetKernel (driftSemigroup v) I := by
  have hconst : Measurable (fun x : E => (driftPath v x : ContinuousPath E)) := by
    have hc : Continuous (ContinuousMap.curry (⟨fun p : E × NNReal => p.1 + (p.2 : ℝ) • v,
        by fun_prop⟩ : C(E × NNReal, E))) := (ContinuousMap.curry _).continuous
    exact hc.measurable
  have hEv : ∀ I : Finset NNReal, Measurable (ContinuousPath.finsetEvaluation (alpha := E) I) := by
    intro I
    rw [measurable_pi_iff]
    intro t
    rw [BorelSpace.measurable_eq (α := E)]
    exact (ContinuousPath.continuous_eval (alpha := E) (t : NNReal)).borel_measurable
  have hmarg : ∀ I : Finset NNReal,
      (Kernel.deterministic _ hconst).map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel (driftSemigroup v) I := by
    intro I
    ext x : 1
    rw [Kernel.map_apply _ (hEv I), Kernel.deterministic_apply, Measure.map_dirac' (hEv I),
      SubMarkovKernelSemigroup.finiteSetKernel_eq_map,
      Kernel.map_apply _ (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I),
      AuxDr_finiteTimeKernel v,
      Measure.map_dirac' (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)]
    congr 1
    funext t
    simp only [SubMarkovKernelSemigroup.orderedPathToFiniteSet,
      SubMarkovKernelSemigroup.finiteSetTimes]
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
    rfl
  refine ⟨Kernel.deterministic _ hconst, ⟨inferInstance, hmarg⟩, ?_⟩
  rintro Q ⟨hQM, hQ⟩
  have key : ∀ (I : Finset DenseTime) (R : Kernel E (ContinuousPath E)),
      (R.map ContinuousPath.denseRestriction).map I.restrict =
        (R.map (ContinuousPath.finsetEvaluation (SubMarkovKernelSemigroup.denseTimePhysicalSet I))).map
          (DenseTimePath.pullbackPhysicalSet I) := by
    intro I R
    have hfun : I.restrict ∘ ContinuousPath.denseRestriction =
        DenseTimePath.pullbackPhysicalSet I ∘
          ContinuousPath.finsetEvaluation (alpha := E)
            (SubMarkovKernelSemigroup.denseTimePhysicalSet I) := by
      funext path
      exact (DenseTimePath.pullbackPhysicalSet_evaluation I path).symm
    rw [← Kernel.map_comp_right _ ContinuousPath.measurable_denseRestriction
      (Finset.measurable_restrict I), hfun,
      Kernel.map_comp_right _ (hEv _) (DenseTimePath.measurable_pullbackPhysicalSet I)]
  have hd : Q.map ContinuousPath.denseRestriction =
      (Kernel.deterministic _ hconst).map ContinuousPath.denseRestriction := by
    apply Kernel.p2m_embedded_cf5a87fc6ca47934
    intro I
    rw [key, key, hQ, hmarg]
  have hemb := ContinuousPath.measurableEmbedding_denseRestriction (alpha := E)
  ext x s hs
  have h1 := congrArg (fun R => R x (ContinuousPath.denseRestriction '' s)) hd
  simp only [Kernel.map_apply _ ContinuousPath.measurable_denseRestriction] at h1
  rw [hemb.map_apply, hemb.map_apply, hemb.injective.preimage_image] at h1
  exact h1
