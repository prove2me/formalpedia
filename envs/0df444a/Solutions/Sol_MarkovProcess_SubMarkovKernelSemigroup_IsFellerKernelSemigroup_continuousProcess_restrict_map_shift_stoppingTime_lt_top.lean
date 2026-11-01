-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:14:20.022392+00:00
-- url     : https://prove2.me/submissions/285f62bf-100c-446f-9c79-63863faee2cf

import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Trajectory_StoppingLtTop_f2bd051e
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
import Theorems.Thm_MarkovProcess_StoppingTime_iUnion_stoppingTimeSlice
import Theorems.Thm_MarkovProcess_StoppingTime_pairwise_disjoint_stoppingTimeSlice
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_continuousPathTrajectory_restrict_map_shift_stoppingTime

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Measurability of random shifts of continuous paths

Shifting a continuous path by a Borel measurable random time, and evaluating it at that time,
are Borel measurable, because the deterministic shift and the evaluation are jointly continuous
in the time and the path.  A finite `NNReal`-valued stopping time for the canonical filtration is
such a random time.  No countable-range premise is used.

This is ordinary measurability infrastructure.  It proves no restart identity and no conditional
expectation formula; those are in `Trajectory/FellerStoppingRestart.lean` and
`Trajectory/FellerStoppingConditional.lean`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- Shifting by a Borel measurable random time is Borel measurable. -/
theorem measurable_shift_of_measurable (T : ContinuousPath alpha → NNReal)
    (hT : Measurable T) :
    Measurable (fun omega ↦ shift (T omega) omega) := by
  have hpair : Measurable (fun omega : ContinuousPath alpha ↦ (T omega, omega)) :=
    hT.prodMk measurable_id
  exact (continuous_shift (alpha := alpha)).measurable.comp hpair

variable [MeasurableSpace alpha] [BorelSpace alpha]









end ContinuousPath
end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The continuous-path Markov process of a Feller semigroup

This is the entry point of the library: for a conservative sub-Markov kernel semigroup `P` on a
nonempty, locally compact Polish state space it names the continuous-path process
`continuousProcess P hP`, restates under quotable names the properties proved for that process
elsewhere in the library, and proves that it is the unique Markov kernel into continuous paths
with the finite-dimensional distributions of `P`.

Every statement carries the Kolmogorov regularity hypothesis `P.KolmogorovRegular hP`, which is
what gives the dense-time trajectory of `P` a continuous modification.  The shift and restart
statements carry in addition the Feller hypothesis `P.IsFellerKernelSemigroup`; the uniqueness
statements carry neither Feller continuity nor local compactness.

Nothing here asserts a Hunt-process property, and no statement covers a stopping time that can be
infinite.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

section FinsetEvaluation

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]



end ContinuousPath

end FinsetEvaluation

namespace Kernel

noncomputable section DenseFiniteEvaluation

variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [MeasurableSpace beta]



section Identification

variable [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]



end Identification

end DenseFiniteEvaluation

end Kernel

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



















variable [LocallyCompactSpace alpha]







/-- Strong Markov property at a finite stopping time, in restart form: after restriction to an
event of the stopped sigma-algebra, the law of the path shifted at the stopping time is the
process started from the state at that time. -/
theorem IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (x : alpha) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (A : Set (ContinuousPath alpha)) (hA : MeasurableSet[hT.measurableSpace] A) :
    (((continuousProcess P hP) x).restrict A).map
        (fun omega ↦ ContinuousPath.shift (T omega) omega) =
      Kernel.comap (continuousProcess P hP) (fun omega ↦ omega (T omega))
          (ContinuousPath.measurable_eval_stoppingTime_borel T hT) ∘ₘ
        (((continuousProcess P hP) x).restrict A) :=
  hFeller.continuousPathTrajectory_restrict_map_shift_stoppingTime P hP _ hK x T hT A hA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]




















end


end SubMarkovKernelSemigroup

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The strong Markov property at a stopping time that may be infinite

Mathlib's stopping times take values in `WithTop ℝ≥0`, so a stopping time of the canonical
filtration on continuous-path space may be infinite, while the strong Markov property of
`MarkovProcess/Main.lean` is stated for finite, `ℝ≥0`-valued stopping times.  This file removes
that restriction on the event `{tau < ⊤}` where the time is finite, writing the finite value as
`(tau omega).untopD 0`:

* `IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top`: the
  restart identity, after restricting the law of the process to `A ∩ {tau < ⊤}` for an event `A`
  of the stopped sigma-algebra;
* `IsFellerKernelSemigroup.continuousProcess_condExp_shift_stoppingTime_lt_top`: the same fact
  in conditional-expectation form, for a bounded strongly measurable functional of the shifted
  path, with the indicator of `{tau < ⊤}` on both sides.
* `StoppingTime.lintegral_mul_indicator_of_restrict_map`: integration of a restricted restart
  identity against a nonnegative weight measurable at the conditioning sigma-algebra.

The route is truncation: `truncTime tau K` is the finite stopping time `min tau K`, and the
slices `stoppingTimeSlice A tau K` partition `A ∩ {tau < ⊤}` into countably many events on which
`tau` is finite and bounded by `K`.  On each slice the finite theorems of `Main.lean` apply, and
both sides of the restart identity are countably additive in the restricted measure; the
conditional-expectation form is then obtained from the slicewise restart identity through a
generic indicator bridge, `condExp_indicator_ae_eq_integral_kernel_of_restrict_map`.

Nothing is asserted about the event `{tau = ⊤}`: on it the shifted path is the path itself, and
neither statement constrains it.  No Hunt-process property is claimed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Function

namespace MarkovProcess

/-! Generic stopping-time material: truncation at a deterministic horizon, the countable slicing
of the event where a `WithTop`-valued stopping time is finite, and the reassembly of restart
identities over the slices.  Nothing here is specific to path space. -/

namespace StoppingTime

section RestrictedRestartIntegral

variable {Omega beta : Type*} {m mOmega : MeasurableSpace Omega}
  {mBeta : MeasurableSpace beta}



end RestrictedRestartIntegral

section Trunc

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}





/-- Below the horizon the truncated time is the untopped time itself. -/
theorem truncTime_eq_untopD {tau : Omega → WithTop NNReal} {K : NNReal} {omega : Omega}
    (h : tau omega ≤ (K : WithTop NNReal)) :
    truncTime tau K omega = (tau omega).untopD 0 := by
  rw [truncTime, min_eq_left h]



/-- Pointwise equal stopping times have the same stopped sigma-algebra. -/
theorem measurableSpace_stoppingTime_congr {f : Filtration NNReal mOmega}
    {tau sigma : Omega → WithTop NNReal}
    (htau : IsStoppingTime f tau) (hsigma : IsStoppingTime f sigma)
    (h : ∀ omega, tau omega = sigma omega) :
    htau.measurableSpace = hsigma.measurableSpace := by
  have hfun : tau = sigma := funext h
  subst hfun
  rfl

/-- The stopped sigma-algebra of a truncated stopping time is the stopped sigma-algebra of the
minimum of the time and the constant horizon. -/
theorem measurableSpace_truncTime {f : Filtration NNReal mOmega} {tau : Omega → WithTop NNReal}
    (htau : IsStoppingTime f tau) (K : NNReal) :
    (isStoppingTime_truncTime htau K).measurableSpace = (htau.min_const K).measurableSpace :=
  measurableSpace_stoppingTime_congr _ _ (coe_truncTime tau K)

end Trunc

section Slices

variable {Omega : Type*} {mOmega : MeasurableSpace Omega} {f : Filtration NNReal mOmega}
  {tau : Omega → WithTop NNReal}







/-- Each slice of an event of the stopped sigma-algebra of `tau` lies in the stopped
sigma-algebra of `tau` truncated at the corresponding horizon. -/
theorem measurableSet_stoppingTimeSlice (htau : IsStoppingTime f tau) {A : Set Omega}
    (hA : MeasurableSet[htau.measurableSpace] A) (K : ℕ) :
    MeasurableSet[(htau.min_const ((K : NNReal))).measurableSpace] (stoppingTimeSlice A tau K) := by
  refine (htau.measurableSet_inter_le_const_iff _ ((K : NNReal))).mp ?_
  refine (hA.inter ?_).inter (htau.measurableSet_le' (K : NNReal))
  refine MeasurableSet.biInter (Set.to_countable _) fun j _ ↦ ?_
  exact htau.measurableSet_gt' (j : NNReal)

/-- Each slice of an event of the stopped sigma-algebra is measurable in the ambient
sigma-algebra. -/
theorem measurableSet_stoppingTimeSlice' (htau : IsStoppingTime f tau) {A : Set Omega}
    (hA : MeasurableSet[htau.measurableSpace] A) (K : ℕ) :
    MeasurableSet (stoppingTimeSlice A tau K) :=
  (htau.min_const ((K : NNReal))).measurableSpace_le _
    (measurableSet_stoppingTimeSlice htau hA K)





/-- On the `K`-th slice the time truncated at `K` is the untopped time itself. -/
theorem truncTime_eq_untopD_of_mem_stoppingTimeSlice {A : Set Omega} {K : ℕ} {omega : Omega}
    (h : omega ∈ stoppingTimeSlice A tau K) :
    truncTime tau (K : NNReal) omega = (tau omega).untopD 0 :=
  truncTime_eq_untopD h.2

end Slices

section Reassembly

variable {Omega beta : Type*} [MeasurableSpace Omega] [MeasurableSpace beta]

/-- A restart identity for the measure restricted to each member of a countable disjoint family
of measurable events holds for the measure restricted to their union: both sides of the identity
are countably additive in the restricted measure. -/
theorem map_restrict_iUnion_eq_comp_of_forall (mu : Measure Omega) (kappa : Kernel Omega beta)
    (g : Omega → beta) (hg : Measurable g) (D : ℕ → Set Omega)
    (hD : ∀ i, MeasurableSet (D i)) (hdisj : Pairwise (Disjoint on D))
    (h : ∀ i, (mu.restrict (D i)).map g = kappa ∘ₘ (mu.restrict (D i))) :
    (mu.restrict (⋃ i, D i)).map g = kappa ∘ₘ (mu.restrict (⋃ i, D i)) := by
  ext s hs
  rw [Measure.bind_apply hs kappa.aemeasurable, Measure.map_apply hg hs,
    Measure.restrict_apply (hg hs), Set.inter_iUnion,
    measure_iUnion (fun i j hij ↦ (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right)
      (fun i ↦ (hg hs).inter (hD i)),
    lintegral_iUnion hD hdisj]
  refine tsum_congr fun i ↦ ?_
  rw [← Measure.restrict_apply (hg hs), ← Measure.map_apply hg hs, h i,
    Measure.bind_apply hs kappa.aemeasurable]

end Reassembly

end StoppingTime

open StoppingTime

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]
  [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]



omit [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha] in
/-- Shifting a path by the untopped value of a stopping time of the canonical filtration is
Borel measurable. -/
theorem measurable_shift_untopD_stoppingTime (tau : ContinuousPath alpha → WithTop NNReal)
    (htau : IsStoppingTime (canonicalFiltration (alpha := alpha)) tau) :
    Measurable (fun omega ↦ shift ((tau omega).untopD 0) omega) :=
  measurable_shift_of_measurable _ (measurable_untopD_stoppingTime tau htau)





end ContinuousPath

namespace StoppingTime

section Bridge

variable {Omega beta E : Type*} {m : MeasurableSpace Omega}
  {mOmega : MeasurableSpace Omega} {mBeta : MeasurableSpace beta}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]





end Bridge

end StoppingTime

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]



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
# The strong Markov property at a stopping time that may be infinite

Mathlib's stopping times take values in `WithTop ℝ≥0`, so a stopping time of the canonical
filtration on continuous-path space may be infinite, while the strong Markov property of
`MarkovProcess/Main.lean` is stated for finite, `ℝ≥0`-valued stopping times.  This file removes
that restriction on the event `{tau < ⊤}` where the time is finite, writing the finite value as
`(tau omega).untopD 0`:

* `IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top`: the
  restart identity, after restricting the law of the process to `A ∩ {tau < ⊤}` for an event `A`
  of the stopped sigma-algebra;
* `IsFellerKernelSemigroup.continuousProcess_condExp_shift_stoppingTime_lt_top`: the same fact
  in conditional-expectation form, for a bounded strongly measurable functional of the shifted
  path, with the indicator of `{tau < ⊤}` on both sides.
* `StoppingTime.lintegral_mul_indicator_of_restrict_map`: integration of a restricted restart
  identity against a nonnegative weight measurable at the conditioning sigma-algebra.

The route is truncation: `truncTime tau K` is the finite stopping time `min tau K`, and the
slices `stoppingTimeSlice A tau K` partition `A ∩ {tau < ⊤}` into countably many events on which
`tau` is finite and bounded by `K`.  On each slice the finite theorems of `Main.lean` apply, and
both sides of the restart identity are countably additive in the restricted measure; the
conditional-expectation form is then obtained from the slicewise restart identity through a
generic indicator bridge, `condExp_indicator_ae_eq_integral_kernel_of_restrict_map`.

Nothing is asserted about the event `{tau = ⊤}`: on it the shifted path is the path itself, and
neither statement constrains it.  No Hunt-process property is claimed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Function


/-! Generic stopping-time material: truncation at a deterministic horizon, the countable slicing
of the event where a `WithTop`-valued stopping time is finite, and the reassembly of restart
identities over the slices.  Nothing here is specific to path space. -/


open StoppingTime





open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (x : alpha) (tau : ContinuousPath alpha → WithTop NNReal)
    (htau : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha)) tau)
    (A : Set (ContinuousPath alpha)) (hA : MeasurableSet[htau.measurableSpace] A) :
    (((continuousProcess P hP) x).restrict (A ∩ {omega | tau omega < ⊤})).map
        (fun omega ↦ ContinuousPath.shift ((tau omega).untopD 0) omega) =
      Kernel.comap (continuousProcess P hP) (fun omega ↦ omega ((tau omega).untopD 0))
          (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau) ∘ₘ
        (((continuousProcess P hP) x).restrict (A ∩ {omega | tau omega < ⊤})) := by
  have hslice : ∀ K : ℕ,
      ((((continuousProcess P hP) x).restrict (stoppingTimeSlice A tau K)).map
          (fun omega ↦ ContinuousPath.shift ((tau omega).untopD 0) omega)) =
        Kernel.comap (continuousProcess P hP) (fun omega ↦ omega ((tau omega).untopD 0))
            (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau) ∘ₘ
          (((continuousProcess P hP) x).restrict (stoppingTimeSlice A tau K)) := by
    intro K
    have hDK : MeasurableSet (stoppingTimeSlice A tau K) :=
      measurableSet_stoppingTimeSlice' htau hA K
    have hAK : MeasurableSet[(isStoppingTime_truncTime htau (K : NNReal)).measurableSpace]
        (stoppingTimeSlice A tau K) := by
      rw [measurableSpace_truncTime htau (K : NNReal)]
      exact measurableSet_stoppingTimeSlice htau hA K
    have hmain := hFeller.continuousProcess_restrict_map_shift_stoppingTime P hP hK x
      (truncTime tau (K : NNReal)) (isStoppingTime_truncTime htau (K : NNReal))
      (stoppingTimeSlice A tau K) hAK
    have hL : ((((continuousProcess P hP) x).restrict (stoppingTimeSlice A tau K)).map
          (fun omega ↦ ContinuousPath.shift (truncTime tau (K : NNReal) omega) omega)) =
        ((((continuousProcess P hP) x).restrict (stoppingTimeSlice A tau K)).map
          (fun omega ↦ ContinuousPath.shift ((tau omega).untopD 0) omega)) := by
      refine Measure.map_congr ((ae_restrict_iff' hDK).mpr (ae_of_all _ fun omega homega ↦ ?_))
      exact congrArg (fun s ↦ ContinuousPath.shift s omega)
        (truncTime_eq_untopD_of_mem_stoppingTimeSlice homega)
    have hR : (Kernel.comap (continuousProcess P hP)
            (fun omega ↦ omega (truncTime tau (K : NNReal) omega))
            (ContinuousPath.measurable_eval_stoppingTime_borel (truncTime tau (K : NNReal))
              (isStoppingTime_truncTime htau (K : NNReal))) ∘ₘ
          (((continuousProcess P hP) x).restrict (stoppingTimeSlice A tau K))) =
        Kernel.comap (continuousProcess P hP) (fun omega ↦ omega ((tau omega).untopD 0))
            (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau) ∘ₘ
          (((continuousProcess P hP) x).restrict (stoppingTimeSlice A tau K)) := by
      refine Measure.comp_congr ((ae_restrict_iff' hDK).mpr (ae_of_all _ fun omega homega ↦ ?_))
      simp only [Kernel.comap_apply]
      rw [truncTime_eq_untopD_of_mem_stoppingTimeSlice homega]
    rw [← hL, hmain, hR]
  rw [← iUnion_stoppingTimeSlice (tau := tau) A]
  exact map_restrict_iUnion_eq_comp_of_forall _ _ _
    (ContinuousPath.measurable_shift_untopD_stoppingTime tau htau) (stoppingTimeSlice A tau)
    (fun K ↦ measurableSet_stoppingTimeSlice' htau hA K)
    (pairwise_disjoint_stoppingTimeSlice A) hslice
