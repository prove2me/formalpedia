-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousPathTrajectory_restrict_map_shift_stoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:59:14.559129+00:00
-- url     : https://prove2.me/submissions/4aa63db8-acfe-4b9d-8fe8-ab0a6612f2ce

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Feller_DensePhysicalFiniteSetContinuity_75f8b26c
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Path_Polish_87f91693
import Definitions.Def_MarkovProcess_V3H_Path_RandomShiftMeasurability_fbe17c52
import Definitions.Def_MarkovProcess_V3H_Path_ShiftCompactTestConvergence_fc2b2de1
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Definitions.Def_MarkovProcess_V3H_Path_StoppingTimeDyadicCeiling_2d75c809
import Definitions.Def_MarkovProcess_V3H_Trajectory_DenseRestrictionMarginals_931e4c17
import Definitions.Def_MarkovProcess_V3H_Trajectory_FellerRestrictedRestart_8026f3b2
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
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
import Theorems.Thm_MarkovProcess_ContinuousPath_restrict_map_shift_stoppingTime_eq_pathKernel_comp_of_restart_on_range
import Theorems.Thm_MarkovProcess_Measure_eq_of_map_finiteRestriction_eq
import Theorems.Thm_MarkovProcess_Measure_map_denseRestriction_injective
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_continuousPathTrajectory_integral_map_denseRestriction_map_restrict_comp_comap
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_norm_integral_map_finiteSetKernel_pullbackPhysicalSet_le
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_continuousPathTrajectory_restrict_map_shift
import Theorems.Thm_MarkovProcess_tendsto_integral_continuousPath_finiteDenseEvaluation_shift_randomTime_of_tendsto

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Integrals of finite dense-time marginals of a path measure

Integrating a compactly supported test against the finite dense-time marginal of a measure on
continuous-path space is integrating the composed test against the measure itself.  This is a
change-of-variables identity with no probabilistic content.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped CompactlySupported

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha] [SecondCountableTopology alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

/-- A compactly supported test integrated against a finite dense-time marginal of a path measure
is the composed test integrated against the path measure. -/
theorem integral_map_denseRestriction_map_restrict
    (nu : Measure (ContinuousPath alpha)) (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) :
    ∫ z, f z ∂((nu.map denseRestriction).map J.restrict) =
      ∫ omega, f (J.restrict (denseRestriction omega)) ∂nu := by
  have hdense := measurable_denseRestriction (alpha := alpha)
  have hrestrict := Finset.measurable_restrict (X := fun _ ↦ alpha) J
  rw [Measure.map_map hrestrict hdense]
  exact integral_map (hrestrict.comp hdense).aemeasurable
    f.continuous.stronglyMeasurable.aestronglyMeasurable

end ContinuousPath
end MarkovProcess


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





/-- Shifting by a finite stopping time for the canonical filtration is Borel measurable. -/
theorem measurable_shift_stoppingTime (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable (fun omega ↦ shift (T omega) omega) :=
  measurable_shift_of_measurable T (measurable_of_isStoppingTime T hT)



end ContinuousPath
end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dominated convergence for tests along random times

This file records path-side dominated-convergence tools for a sequence of measurable random
times converging pointwise to a limiting random time.  The measure is any finite measure on
continuous-path space; no Markov or kernel assumption is used.  The deterministic-sequence
versions are in `ContinuousPathShiftCompactTestConvergence.lean`.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty CompactlySupported

namespace MarkovProcess

noncomputable section

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]

/-- Integrals of a bounded continuous state observable at pointwise convergent measurable random
times converge under any finite path measure. -/
theorem tendsto_integral_continuousPath_eval_randomTime_of_tendsto
    (mu : Measure (ContinuousPath alpha)) [IsFiniteMeasure mu]
    (T : ℕ → ContinuousPath alpha → NNReal) (Tlim : ContinuousPath alpha → NNReal)
    (hT : ∀ n, Measurable (T n))
    (hlim : ∀ omega, Tendsto (fun n ↦ T n omega) atTop (nhds (Tlim omega)))
    (g : alpha → ℝ) (hg : Continuous g) (C : ℝ) (hgC : ∀ y, ‖g y‖ ≤ C) :
    Tendsto (fun n ↦ ∫ omega, g (omega (T n omega)) ∂mu) atTop
      (nhds (∫ omega, g (omega (Tlim omega)) ∂mu)) := by
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [] with n
    exact ((hg.measurable.comp
      (ContinuousPath.measurable_eval_of_measurable (T n) (hT n))).stronglyMeasurable
      ).aestronglyMeasurable
  · exact ⟨C, Filter.Eventually.of_forall fun n ↦ ae_of_all _ fun omega ↦ hgC _⟩
  · filter_upwards [] with omega
    exact hg.continuousAt.tendsto.comp
      (omega.continuous.continuousAt.tendsto.comp (hlim omega))



end

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dyadic ceiling approximation of finite stopping times

The level-`n` dyadic ceiling of a nonnegative time is the least point of the grid `2⁻ⁿ ℕ` that is
at least the time.  Composed with a finite `NNReal`-valued stopping time it produces stopping
times with countable range that decrease to the original time.  This is ordinary stopping-time
infrastructure and proves no restart identity; the restart identity obtained from this
approximation is in `Trajectory/FellerStoppingRestart.lean`.
-/

open MeasureTheory Filter Topology
open scoped NNReal

namespace MarkovProcess

noncomputable section





/-- The real coercion of a dyadic ceiling is its defining quotient. -/
private theorem coe_dyadicCeiling (n : ℕ) (t : NNReal) :
    ((dyadicCeiling n t : NNReal) : ℝ) = (⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ : ℝ) / 2 ^ n := rfl

/-- The real coercion of a dyadic floor is its defining quotient. -/
private theorem coe_dyadicFloor (n : ℕ) (t : NNReal) :
    ((dyadicFloor n t : NNReal) : ℝ) = (⌊(2 ^ n : ℝ) * (t : ℝ)⌋₊ : ℝ) / 2 ^ n := rfl

/-- The level-`n` dyadic ceiling is at least the time it approximates. -/
theorem le_dyadicCeiling (n : ℕ) (t : NNReal) : t ≤ dyadicCeiling n t := by
  rw [← NNReal.coe_le_coe, coe_dyadicCeiling, le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
  calc (t : ℝ) * 2 ^ n = (2 ^ n : ℝ) * (t : ℝ) := by ring
    _ ≤ (⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ : ℝ) := Nat.le_ceil _

/-- The level-`n` dyadic floor is at most the time it approximates. -/
theorem dyadicFloor_le (n : ℕ) (t : NNReal) : dyadicFloor n t ≤ t := by
  rw [← NNReal.coe_le_coe, coe_dyadicFloor, div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
  calc (⌊(2 ^ n : ℝ) * (t : ℝ)⌋₊ : ℝ) ≤ (2 ^ n : ℝ) * (t : ℝ) := Nat.floor_le (by positivity)
    _ = (t : ℝ) * 2 ^ n := by ring

/-- The level-`n` dyadic ceiling overshoots by at most one grid step. -/
theorem dyadicCeiling_le_add (n : ℕ) (t : NNReal) :
    dyadicCeiling n t ≤ t + (2 ^ n : NNReal)⁻¹ := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hinv : ((2 : ℝ) ^ n)⁻¹ * 2 ^ n = 1 := inv_mul_cancel₀ (ne_of_gt h2)
  rw [← NNReal.coe_le_coe, coe_dyadicCeiling, NNReal.coe_add, NNReal.coe_inv, NNReal.coe_pow,
    NNReal.coe_ofNat, div_le_iff₀ h2]
  calc (⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ : ℝ) ≤ (2 ^ n : ℝ) * (t : ℝ) + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
    _ = ((t : ℝ) + ((2 : ℝ) ^ n)⁻¹) * 2 ^ n := by rw [add_mul, hinv]; ring

/-- The ceiling comparison rewritten as an inequality between natural indices. -/
private theorem dyadicCeiling_le_iff_nat (n : ℕ) (t i : NNReal) :
    dyadicCeiling n t ≤ i ↔ ⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ ≤ ⌊(2 ^ n : ℝ) * (i : ℝ)⌋₊ := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hfloor : ⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ ≤ ⌊(2 ^ n : ℝ) * (i : ℝ)⌋₊ ↔
      ((⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ : ℕ) : ℝ) ≤ (2 ^ n : ℝ) * (i : ℝ) :=
    Nat.le_floor_iff (by positivity)
  rw [← NNReal.coe_le_coe, coe_dyadicCeiling, div_le_iff₀ h2, hfloor,
    mul_comm ((2 : ℝ) ^ n) (i : ℝ)]

/-- The floor comparison rewritten as the same inequality between natural indices. -/
private theorem le_dyadicFloor_iff_nat (n : ℕ) (t i : NNReal) :
    t ≤ dyadicFloor n i ↔ ⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ ≤ ⌊(2 ^ n : ℝ) * (i : ℝ)⌋₊ := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [← NNReal.coe_le_coe, coe_dyadicFloor, le_div_iff₀ h2, Nat.ceil_le,
    mul_comm ((2 : ℝ) ^ n) (t : ℝ)]

/-- The dyadic ceiling lies below a time exactly when the time's dyadic floor lies above. -/
theorem dyadicCeiling_le_iff (n : ℕ) (t i : NNReal) :
    dyadicCeiling n t ≤ i ↔ t ≤ dyadicFloor n i :=
  (dyadicCeiling_le_iff_nat n t i).trans (le_dyadicFloor_iff_nat n t i).symm



/-- The dyadic ceilings of a fixed time converge to that time. -/
theorem tendsto_dyadicCeiling (t : NNReal) :
    Tendsto (fun n ↦ dyadicCeiling n t) atTop (𝓝 t) := by
  have hhalf : ((2 : NNReal))⁻¹ < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_inv, NNReal.coe_ofNat, NNReal.coe_one]
    norm_num
  have hinv : Tendsto (fun n : ℕ ↦ (2 ^ n : NNReal)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hhalf
  have hupper : Tendsto (fun n : ℕ ↦ t + (2 ^ n : NNReal)⁻¹) atTop (𝓝 t) := by
    simpa only [add_zero] using tendsto_const_nhds.add hinv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n ↦ le_dyadicCeiling n t) (fun n ↦ dyadicCeiling_le_add n t)











/-- Each dyadic level has only countably many ceiling values. -/
theorem countable_range_dyadicCeiling (n : ℕ) : (Set.range (dyadicCeiling n)).Countable := by
  refine (Set.countable_range (dyadicGrid n)).mono ?_
  rintro x ⟨t, rfl⟩
  exact ⟨⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊, rfl⟩

variable {Omega : Type*} {m : MeasurableSpace Omega}

/-- The dyadic ceiling of any time-valued map has countable range. -/
theorem countable_range_dyadicCeiling_comp (n : ℕ) (T : Omega → NNReal) :
    (Set.range fun omega ↦ dyadicCeiling n (T omega)).Countable := by
  refine (countable_range_dyadicCeiling n).mono ?_
  rintro x ⟨omega, rfl⟩
  exact ⟨T omega, rfl⟩





/-- The dyadic ceiling of a finite stopping time is a stopping time for the same filtration. -/
theorem isStoppingTime_dyadicCeiling {f : Filtration NNReal m} {T : Omega → NNReal}
    (hT : IsStoppingTime f (fun omega ↦ (T omega : WithTop NNReal))) (n : ℕ) :
    IsStoppingTime f (fun omega ↦ (dyadicCeiling n (T omega) : WithTop NNReal)) := by
  intro i
  refine (f.mono (dyadicFloor_le n i) _ (hT (dyadicFloor n i))).congr ?_
  ext omega
  simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]
  exact (dyadicCeiling_le_iff n (T omega) i).symm

end

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Event-restricted restart of the Feller trajectory at finite stopping times

The canonical continuous trajectory of a conservative Feller kernel semigroup restarts after
restriction to an event in the stopped sigma-algebra of any finite `NNReal`-valued stopping time
for the canonical filtration.  The proof approximates the stopping time from above by its dyadic
ceilings, which have countable range, applies the all-time deterministic restart identity on
their level sets, identifies every finite dense future marginal by compact tests and dominated
convergence, and concludes by measure identification on dense restrictions.

The stopping time here is finite and `NNReal`-valued.  A `WithTop`-valued time that can be
infinite is covered, on the event where it is finite, in `Trajectory/StoppingLtTop.lean`; no
Hunt-process property is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal CompactlySupported ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]



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
# Event-restricted restart of the Feller trajectory at finite stopping times

The canonical continuous trajectory of a conservative Feller kernel semigroup restarts after
restriction to an event in the stopped sigma-algebra of any finite `NNReal`-valued stopping time
for the canonical filtration.  The proof approximates the stopping time from above by its dyadic
ceilings, which have countable range, applies the all-time deterministic restart identity on
their level sets, identifies every finite dense future marginal by compact tests and dominated
convergence, and concludes by measure identification on dense restrictions.

The stopping time here is finite and `NNReal`-valued.  A `WithTop`-valued time that can be
infinite is covered, on the event where it is finite, in `Trajectory/StoppingLtTop.lean`; no
Hunt-process property is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal CompactlySupported ZeroAtInfty

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    ∀ A : Set (ContinuousPath alpha), MeasurableSet[hT.measurableSpace] A →
      (((continuousPathTrajectory P hP default) x).restrict A).map
          (fun omega ↦ ContinuousPath.shift (T omega) omega) =
        Kernel.comap (continuousPathTrajectory P hP default)
            (fun omega ↦ omega (T omega))
            (ContinuousPath.measurable_eval_stoppingTime_borel T hT) ∘ₘ
          (((continuousPathTrajectory P hP default) x).restrict A) := by
  intro A hA
  set Q := continuousPathTrajectory P hP default with hQ
  set mu := (Q x).restrict A with hmu
  set Tn : ℕ → ContinuousPath alpha → NNReal := fun n omega ↦ dyadicCeiling n (T omega) with hTn
  have hTnStop : ∀ n, IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ ((Tn n omega : NNReal) : WithTop NNReal)) :=
    fun n ↦ isStoppingTime_dyadicCeiling hT n
  have hTnMeas : ∀ n, Measurable (Tn n) :=
    fun n ↦ ContinuousPath.measurable_of_isStoppingTime _ (hTnStop n)
  have hATn : ∀ n, MeasurableSet[(hTnStop n).measurableSpace] A := fun n ↦
    IsStoppingTime.measurableSpace_mono hT (hTnStop n)
      (fun omega ↦ WithTop.coe_le_coe.mpr (le_dyadicCeiling n (T omega))) A hA
  have hstep : ∀ n, mu.map (fun omega ↦ ContinuousPath.shift (Tn n omega) omega) =
      Kernel.comap Q (fun omega ↦ omega (Tn n omega))
        (ContinuousPath.measurable_eval_stoppingTime_borel _ (hTnStop n)) ∘ₘ mu := fun n ↦
    ContinuousPath.restrict_map_shift_stoppingTime_eq_pathKernel_comp_of_restart_on_range
      Q x (Tn n) (hTnStop n) (countable_range_dyadicCeiling_comp n T)
      (fun S _ ↦ hFeller.continuousPathTrajectory_restrict_map_shift P hP default hK x S)
      A (hATn n)
  apply MarkovProcess.Measure.map_denseRestriction_injective
  apply MarkovProcess.Measure.eq_of_map_finiteRestriction_eq
  intro J
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  set L : Kernel alpha (J → alpha) :=
    (finiteSetKernel P (denseTimePhysicalSet J)).map
      (DenseTimePath.pullbackPhysicalSet J) with hL
  set g : alpha → ℝ := fun y ↦ ∫ z, f z ∂L y with hg
  have hg_cont : Continuous g :=
    hFeller.continuous_integral_map_finiteSetKernel_pullbackPhysicalSet hP J f
  set C := ‖PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f‖ with hC
  have hg_bound : ∀ y, ‖g y‖ ≤ C := fun y ↦
    hP.norm_integral_map_finiteSetKernel_pullbackPhysicalSet_le J f y
  have hlimT : ∀ omega, Tendsto (fun n ↦ Tn n omega) atTop (nhds (T omega)) :=
    fun omega ↦ tendsto_dyadicCeiling (T omega)
  have hright := tendsto_integral_continuousPath_eval_randomTime_of_tendsto
    mu Tn T hTnMeas hlimT g hg_cont C hg_bound
  have hleft := tendsto_integral_continuousPath_finiteDenseEvaluation_shift_randomTime_of_tendsto
    mu Tn T hTnMeas hlimT J f
  have htest : StronglyMeasurable (fun omega : ContinuousPath alpha ↦
      f (J.restrict (ContinuousPath.denseRestriction omega))) :=
    (f.continuous.comp (ContinuousPath.continuous_finiteEvaluation
      (fun j : J ↦ DenseTime.castOrderEmbedding j))).stronglyMeasurable
  have heq : ∀ n, (∫ omega, f (fun j : J ↦
        omega (Tn n omega + DenseTime.castOrderEmbedding j)) ∂mu) =
      ∫ omega, g (omega (Tn n omega)) ∂mu := by
    intro n
    have hm := congrArg (fun rho : Measure (ContinuousPath alpha) ↦
      (rho.map ContinuousPath.denseRestriction).map J.restrict) (hstep n)
    have hi := congrArg (fun rho : Measure (J → alpha) ↦ ∫ z, f z ∂rho) hm
    rw [ContinuousPath.integral_map_denseRestriction_map_restrict,
      continuousPathTrajectory_integral_map_denseRestriction_map_restrict_comp_comap
        P hP default hK] at hi
    rw [integral_map
      (ContinuousPath.measurable_shift_of_measurable (Tn n) (hTnMeas n)).aemeasurable
      htest.aestronglyMeasurable] at hi
    simpa only [ContinuousPath.denseRestriction_apply, ContinuousPath.shift_apply, hg, hL]
      using! hi
  have hlimits :
      (∫ omega, f (fun j : J ↦ omega (T omega + DenseTime.castOrderEmbedding j)) ∂mu) =
        ∫ omega, g (omega (T omega)) ∂mu :=
    tendsto_nhds_unique hleft (by simpa only [heq] using hright)
  rw [ContinuousPath.integral_map_denseRestriction_map_restrict,
    continuousPathTrajectory_integral_map_denseRestriction_map_restrict_comp_comap
      P hP default hK]
  rw [integral_map
    (ContinuousPath.measurable_shift_stoppingTime T hT).aemeasurable
    htest.aestronglyMeasurable]
  simpa only [ContinuousPath.denseRestriction_apply, ContinuousPath.shift_apply, hg, hL]
    using! hlimits
