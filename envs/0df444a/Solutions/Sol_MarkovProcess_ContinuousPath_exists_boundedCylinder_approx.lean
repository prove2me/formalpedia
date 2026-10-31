-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.exists_boundedCylinder_approx
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:47:55.042075+00:00
-- url     : https://prove2.me/submissions/28eea2a4-2520-4736-9fb2-9fbd1f7faf02

import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteProductStoneWeierstrass_f57e156f
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Trajectory_CylinderAlgebra_cdb093fb
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
import Theorems.Thm_MarkovProcess_ContinuousPath_coordinateSubalgebra_separatesPoints
import Theorems.Thm_MarkovProcess_ContinuousPath_isBoundedCylinder_of_mem_coordinateSubalgebra

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Cylinder test functions on continuous-path space

A *cylinder* functional of a continuous path reads the path at finitely many times and applies a
bounded continuous function to the values there.  These functionals form an algebra, they
separate points of path space (two distinct continuous paths differ at some time, and functions
vanishing at infinity separate the two values), and therefore, by Stone--Weierstrass, they are
uniformly dense on every compact set of paths.

The approximation is stated in the form that a tightness argument consumes: given a bounded
continuous functional `F` and a compact set of paths `K`, there is a *bounded* cylinder functional
that is uniformly `eps`-close to `F` on `K` and whose norm exceeds `‖F‖` by at most `eps`.  The
norm control matters, because the approximation error off `K` is paid for by the total mass
outside `K` times the sum of the two norms; without it the argument would be circular.

Main results:

* `MarkovProcess.ContinuousPath.IsBoundedCylinder`, the cylinder property, closed under sums,
  products and constants;
* `MarkovProcess.ContinuousPath.coordinateSubalgebra`, the generated algebra of test functions,
  with `coordinateSubalgebra_separatesPoints` and
  `isBoundedCylinder_of_mem_coordinateSubalgebra`;
* `MarkovProcess.ContinuousPath.exists_boundedCylinder_approx`, the Stone--Weierstrass
  approximation with norm control.

Nothing here mentions a probability law, and no continuity in a starting point is asserted.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BoundedContinuousFunction NNReal ZeroAtInfty

namespace MarkovProcess

namespace ContinuousPath

section Cylinder

variable {alpha : Type*} [TopologicalSpace alpha]





















end Cylinder

section Approximation

variable {alpha : Type*} [MetricSpace alpha] [LocallyCompactSpace alpha]



end Approximation

end ContinuousPath

end MarkovProcess


open MarkovProcess
open MarkovProcess.ContinuousPath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Cylinder test functions on continuous-path space

A *cylinder* functional of a continuous path reads the path at finitely many times and applies a
bounded continuous function to the values there.  These functionals form an algebra, they
separate points of path space (two distinct continuous paths differ at some time, and functions
vanishing at infinity separate the two values), and therefore, by Stone--Weierstrass, they are
uniformly dense on every compact set of paths.

The approximation is stated in the form that a tightness argument consumes: given a bounded
continuous functional `F` and a compact set of paths `K`, there is a *bounded* cylinder functional
that is uniformly `eps`-close to `F` on `K` and whose norm exceeds `‖F‖` by at most `eps`.  The
norm control matters, because the approximation error off `K` is paid for by the total mass
outside `K` times the sum of the two norms; without it the argument would be circular.

Main results:

* `MarkovProcess.ContinuousPath.IsBoundedCylinder`, the cylinder property, closed under sums,
  products and constants;
* `MarkovProcess.ContinuousPath.coordinateSubalgebra`, the generated algebra of test functions,
  with `coordinateSubalgebra_separatesPoints` and
  `isBoundedCylinder_of_mem_coordinateSubalgebra`;
* `MarkovProcess.ContinuousPath.exists_boundedCylinder_approx`, the Stone--Weierstrass
  approximation with norm control.

Nothing here mentions a probability law, and no continuity in a starting point is asserted.
-/

open scoped BoundedContinuousFunction NNReal ZeroAtInfty





variable {alpha : Type*} [MetricSpace alpha] [LocallyCompactSpace alpha]

namespace MarkovProcess.ContinuousPath

end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
theorem solution (F : ContinuousPath alpha →ᵇ ℝ)
    {K : Set (ContinuousPath alpha)} (hK : IsCompact K) {eps : ℝ} (heps : 0 < eps) :
    ∃ G : ContinuousPath alpha →ᵇ ℝ, IsBoundedCylinder (fun omega ↦ G omega) ∧
      ‖G‖ ≤ ‖F‖ + eps ∧ ∀ omega ∈ K, |G omega - F omega| ≤ eps := by
  obtain ⟨G0, hG0mem, hG0approx⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (coordinateSubalgebra_separatesPoints (alpha := alpha)) F.toContinuousMap hK heps
  obtain ⟨I, g0, hg0⟩ := isBoundedCylinder_of_mem_coordinateSubalgebra hG0mem
  set C : ℝ := ‖F‖ + eps with hCdef
  have hC0 : 0 ≤ C := by positivity
  set clampC : ℝ → ℝ := fun y ↦ max (-C) (min C y) with hclampdef
  have hclampcont : Continuous clampC :=
    continuous_const.max (continuous_const.min continuous_id)
  have hclampabs : ∀ y, |clampC y| ≤ C := by
    intro y
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hclampeq : ∀ y, |y| ≤ C → clampC y = y := by
    intro y hy
    rw [abs_le] at hy
    simp only [hclampdef, min_eq_right hy.2, max_eq_right hy.1]
  set g : (I → alpha) →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun path ↦ clampC (g0 path))
      (hclampcont.comp g0.continuous) C (fun path ↦ by
        rw [Real.norm_eq_abs]; exact hclampabs _) with hgdef
  set G : ContinuousPath alpha →ᵇ ℝ :=
    g.compContinuous ⟨finsetEvaluation (alpha := alpha) I, continuous_finiteEvaluation _⟩ with hGdef
  have hGapply : ∀ omega : ContinuousPath alpha, G omega = clampC (G0 omega) := by
    intro omega
    rw [hGdef]
    show clampC (g0 (finsetEvaluation I omega)) = clampC (G0 omega)
    congr 1
    exact (hg0 omega).symm
  refine ⟨G, ⟨I, g, fun omega ↦ rfl⟩, ?_, ?_⟩
  · refine (BoundedContinuousFunction.norm_le hC0).mpr fun omega ↦ ?_
    rw [Real.norm_eq_abs, hGapply omega]
    exact hclampabs _
  · intro omega homega
    have hnear : |G0 omega - F omega| < eps := by
      simpa only [Real.norm_eq_abs] using! hG0approx omega homega
    have hFbound : |F omega| ≤ ‖F‖ := by
      simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm omega
    have hG0bound : |G0 omega| ≤ C := by
      have habs : |G0 omega| - |F omega| ≤ |G0 omega - F omega| :=
        abs_sub_abs_le_abs_sub _ _
      rw [hCdef]
      linarith
    rw [hGapply omega, hclampeq _ hG0bound]
    exact hnear.le
