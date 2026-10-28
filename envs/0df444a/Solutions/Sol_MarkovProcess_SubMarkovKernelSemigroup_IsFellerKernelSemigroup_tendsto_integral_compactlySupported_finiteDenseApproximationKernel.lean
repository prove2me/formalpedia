-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.tendsto_integral_compactlySupported_finiteDenseApproximationKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:44:37.994748+00:00
-- url     : https://prove2.me/submissions/7e440fbd-e3bc-49d1-b08f-4aa968610d3a

import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousExtension
import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousLaw
import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicFloor
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Continuity_GlobalDyadicFloorModification
import Definitions.Def_MarkovProcess_Continuity_KolmogorovTimeShift
import Definitions.Def_MarkovProcess_Continuity_ShiftedUnitModification
import Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixRecursion
import Definitions.Def_MarkovProcess_DenseTime_Trajectory
import Definitions.Def_MarkovProcess_Feller_BackwardC0Recursion
import Definitions.Def_MarkovProcess_Feller_Semigroup
import Definitions.Def_MarkovProcess_FiniteTime_CoordinateProductActiveReduction
import Definitions.Def_MarkovProcess_FiniteTime_CoordinateProductNormalization
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductCoordinateNormalForm
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductStoneWeierstrass
import Definitions.Def_MarkovProcess_FiniteTime_FiniteSetKernelCompactTestTransport
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_C0_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_Integral_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_PositiveC0OperatorMeasure
import Definitions.Def_MarkovProcess_Path_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Path_Polish_SourceClosedV3
import Definitions.Def_MarkovProcess_Semigroup_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_DenseTimeHistory
import Definitions.Def_MarkovProcess_Time_FiniteDenseApproximationOrdered
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Definitions.Def_MarkovProcess_Trajectory_AllTimeFiniteMarginals
import Definitions.Def_MarkovProcess_Trajectory_Basic
import Definitions.Def_MarkovProcess_Trajectory_FiniteMarginals
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
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
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Theorems.Thm_MarkovProcess_PiContinuousMap_exists_coordinateC0Subalgebra_near_compactlySupported
import Theorems.Thm_MarkovProcess_PiContinuousMap_exists_coordinateProductTerms_of_mem_coordinateC0Subalgebra
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_finiteTimeKernel_map_restrictPath
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_tendsto_integral_compactlySupported_finiteTimeKernel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Stone--Weierstrass on products

This file packages the subalgebra of real continuous functions on a finite product generated by
one-coordinate functions.  It proves that this subalgebra separates points, and hence is uniformly
dense when the factor is compact.

Membership in `PiContinuousMap.coordinateSubalgebra` expresses precisely that a
function is obtained from one-coordinate functions using finitely many constants, sums, and
products.  Thus the approximation theorem is a reusable bundled form of finite-product test
function density.

The coordinate pullback of a function in `C₀(α, ℝ)` need not itself vanish at infinity on the
whole product.  Accordingly, `coordinateC0Subalgebra` is a subalgebra of continuous maps; the
`C₀` designation records its one-coordinate generators, not its ambient carrier.
-/

open Topology
open scoped ZeroAtInfty

namespace MarkovProcess.PiContinuousMap

variable {I α : Type*} [TopologicalSpace α]



@[simp]
theorem coordinate_apply (i : I) (f : C(α, ℝ)) (x : I → α) :
    coordinate i f x = f (x i) :=
  rfl
end MarkovProcess.PiContinuousMap

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Explicit coordinate-product normal forms

This file replaces abstract membership in the coordinate `C₀` algebra by a concrete finite
sum of finite products.  Factors are stored in lists, so the normal form can subsequently be
consumed by recursion (for example, by iterated kernel integration).  The empty factor list is
the constant function `1`; in particular the representation treats constants and an empty
coordinate type without exceptional cases.
-/

open scoped CompactlySupported ZeroAtInfty

namespace MarkovProcess.PiContinuousMap

variable {I α : Type*} [TopologicalSpace α]





@[simp]
theorem CoordinateProductTerm.toContinuousMap_apply
    (t : CoordinateProductTerm I α) (x : I → α) :
    t.toContinuousMap x = t.coefficient * (t.factors.map (fun p ↦ p.2 (x p.1))).prod := by
  rw [CoordinateProductTerm.toContinuousMap, ContinuousMap.smul_apply, smul_eq_mul]
  congr 1
  induction t.factors with
  | nil => rfl
  | cons p factors ih =>
      simp only [List.map_cons, List.prod_cons, ContinuousMap.mul_apply, coordinate_apply]
      change p.2 (x p.1) * _ = p.2 (x p.1) * _
      exact congrArg (fun z ↦ p.2 (x p.1) * z) ih



@[simp]
theorem coordinatePolynomial_apply (terms : List (CoordinateProductTerm I α)) (x : I → α) :
    coordinatePolynomial terms x =
      (terms.map fun t ↦ t.coefficient * (t.factors.map fun p ↦ p.2 (x p.1)).prod).sum := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
      rw [coordinatePolynomial]
      simp only [List.map_cons, List.sum_cons, ContinuousMap.add_apply,
        CoordinateProductTerm.toContinuousMap_apply]
      change _ + coordinatePolynomial terms x = _
      rw [ih]

@[simp]
theorem coordinatePolynomial_nil :
    coordinatePolynomial ([] : List (CoordinateProductTerm I α)) = 0 :=
  rfl

@[simp]
theorem coordinatePolynomial_cons (t : CoordinateProductTerm I α)
    (terms : List (CoordinateProductTerm I α)) :
    coordinatePolynomial (t :: terms) = t.toContinuousMap + coordinatePolynomial terms :=
  rfl















/-- Every compactly supported continuous finite-product test is uniformly approximable on the
whole product by an explicit finite sum of scalar multiples of coordinate products. -/
theorem exists_coordinateProductTerms_near_compactlySupported
    [Fintype I] [T3Space α] [LocallyCompactSpace α]
    (f : C_c(I → α, ℝ)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ terms : List (CoordinateProductTerm I α),
      ∀ x, ‖(terms.map fun t ↦
        t.coefficient * (t.factors.map fun p ↦ p.2 (x p.1)).prod).sum - f x‖ < epsilon := by
  obtain ⟨h, hh, hnear⟩ :=
    exists_coordinateC0Subalgebra_near_compactlySupported f hepsilon
  obtain ⟨terms, rfl⟩ := exists_coordinateProductTerms_of_mem_coordinateC0Subalgebra hh
  refine ⟨terms, fun x ↦ ?_⟩
  rw [← coordinatePolynomial_apply]
  exact hnear x
end MarkovProcess.PiContinuousMap

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite ordered time families

This file provides increasing finite families of nonnegative times and the elementary operations
for restricting such families and their coordinate paths along order embeddings.  It is an
ordinary finite-dimensional API and makes no probability-law or stochastic-process claim.
-/

namespace MarkovProcess



namespace FiniteOrderedTimes

































/-- Restriction of finite coordinate paths is measurable for product measurable spaces. -/
theorem measurable_restrictPath {m n : ℕ} (e : Fin m ↪o Fin n)
    {α : Type*} [MeasurableSpace α] :
    Measurable (restrictPath e : (Fin n → α) → Fin m → α) :=
  measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (e i)
end FiniteOrderedTimes
end MarkovProcess

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Compact-test transport for finite-set kernels

This file identifies the increasing-coordinate representation of a finite set with its ordinary
function space by a homeomorphism. It transports compactly supported tests across that
homeomorphism and rewrites their finite-set-kernel integrals as finite-time-kernel integrals.

Strong measurability of a compactly supported test is obtained privately from uniform coordinate-
polynomial approximations. This avoids adding an `OpensMeasurableSpace` assumption on the finite
product. These declarations are finite-dimensional infrastructure; no statement about path space
is proved here.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported

namespace MarkovProcess.SubMarkovKernelSemigroup

private theorem stronglyMeasurable_coordinatePolynomial
    {I alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
    (terms : List (PiContinuousMap.CoordinateProductTerm I alpha)) :
    StronglyMeasurable (PiContinuousMap.coordinatePolynomial terms) := by
  induction terms with
  | nil =>
      simp only [PiContinuousMap.coordinatePolynomial_nil]
      exact stronglyMeasurable_const
  | cons term terms ih =>
      rw [PiContinuousMap.coordinatePolynomial_cons]
      apply StronglyMeasurable.add _ ih
      have hprod : StronglyMeasurable (fun path : I → alpha ↦
          (term.factors.map fun p ↦ p.2 (path p.1)).prod) := by
        induction term.factors with
        | nil => exact stronglyMeasurable_const
        | cons p factors ihFactors =>
            simp only [List.map_cons, List.prod_cons]
            exact ((p.2.measurable.comp (measurable_pi_apply p.1)).stronglyMeasurable).mul
              ihFactors
      rw [show (term.toContinuousMap : (I → alpha) → ℝ) = fun path ↦
          term.coefficient * (term.factors.map fun p ↦ p.2 (path p.1)).prod by
        funext path
        exact PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply term path]
      exact hprod.const_mul term.coefficient

private theorem stronglyMeasurable_compactlySupported_pi
    {I alpha : Type*} [Fintype I] [TopologicalSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] [T3Space alpha] [LocallyCompactSpace alpha]
    (f : C_c(I → alpha, ℝ)) : StronglyMeasurable f := by
  have hexists (m : ℕ) :
      ∃ terms : List (PiContinuousMap.CoordinateProductTerm I alpha),
        ∀ x, ‖PiContinuousMap.coordinatePolynomial terms x - f x‖ <
          1 / ((m : ℝ) + 1) := by
    have hpositive : 0 < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨terms, hterms⟩ :=
      PiContinuousMap.exists_coordinateProductTerms_near_compactlySupported f hpositive
    exact ⟨terms, fun x ↦ by
      rw [PiContinuousMap.coordinatePolynomial_apply]
      exact hterms x⟩
  choose terms hterms using hexists
  apply stronglyMeasurable_of_tendsto Filter.atTop
    (fun m ↦ stronglyMeasurable_coordinatePolynomial (terms m))
  rw [tendsto_pi_nhds]
  intro x
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hscalar : Filter.Tendsto (fun m : ℕ ↦ (1 : ℝ) / ((m : ℝ) + 1)) Filter.atTop
      (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Metric.tendsto_nhds] at hscalar
  filter_upwards [hscalar epsilon hepsilon] with m hm
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at hm
  exact (hterms m x).trans_le hm.le



/-- The ordered-coordinate homeomorphism has underlying function `orderedPathToFiniteSet`. -/
@[simp]
theorem orderedPathToFiniteSetHomeomorph_apply
    {alpha : Type*} [TopologicalSpace alpha] (I : Finset NNReal)
    (path : Fin I.card → alpha) :
    orderedPathToFiniteSetHomeomorph I path = orderedPathToFiniteSet I path := by
  ext t
  change (Equiv.piCongrLeft (fun _ : I ↦ alpha) (I.orderIsoOfFin rfl).toEquiv path) t = _
  rw [Equiv.piCongrLeft_apply]
  simp only [orderedPathToFiniteSet]
  rw [eqRec_eq_cast, cast_eq]
  rfl



/-- Evaluation of a compact test pulled back to increasing coordinates. -/
@[simp]
theorem pullbackFiniteSetCompactTest_apply
    {alpha : Type*} [TopologicalSpace alpha] [T2Space alpha]
    (I : Finset NNReal) (f : C_c(I → alpha, ℝ)) (path : Fin I.card → alpha) :
    pullbackFiniteSetCompactTest I f path = f (orderedPathToFiniteSet I path) := by
  rw [pullbackFiniteSetCompactTest]
  exact congr_arg f (orderedPathToFiniteSetHomeomorph_apply I path)

/-- Integration against the mapped ordered-coordinate law equals integration of the pulled-back
compact test. -/
theorem integral_map_orderedPathToFiniteSet
    {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
    (I : Finset NNReal) (f : C_c(I → alpha, ℝ))
    (mu : Measure (Fin I.card → alpha)) :
    ∫ y, f y ∂mu.map (orderedPathToFiniteSet I) =
      ∫ path, pullbackFiniteSetCompactTest I f path ∂mu := by
  rw [integral_map (measurable_orderedPathToFiniteSet I).aemeasurable
    (stronglyMeasurable_compactlySupported_pi f).aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun path ↦ (pullbackFiniteSetCompactTest_apply I f path).symm

/-- A compact-test integral against `finiteSetKernel` is the corresponding pulled-back integral
against `finiteTimeKernel`. -/
theorem integral_finiteSetKernel_eq_integral_pullbackFiniteSetCompactTest
    {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
    (P : SubMarkovKernelSemigroup alpha) (I : Finset NNReal)
    (f : C_c(I → alpha, ℝ)) (x : alpha) :
    ∫ y, f y ∂finiteSetKernel P I x =
      ∫ path, pullbackFiniteSetCompactTest I f path
        ∂finiteTimeKernel P (finiteSetTimes I) x := by
  rw [finiteSetKernel_eq_map, Kernel.map_apply _ (measurable_orderedPathToFiniteSet I)]
  exact integral_map_orderedPathToFiniteSet I f (finiteTimeKernel P (finiteSetTimes I) x)
end MarkovProcess.SubMarkovKernelSemigroup

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Arbitrary-time finite marginals of continuous-path trajectories

This file develops the simultaneous rational approximation needed to pass from the already
identified rational finite-dimensional distributions to finite families of arbitrary
nonnegative real times.  It proves the path-side dominated-convergence argument, identifies every
rational approximating law with the existing finite-set kernel, and reduces the desired equality
to compactly-supported-test convergence of those finite-set kernels.

The remaining Feller analytic statement is not claimed here: one must still prove that the
recursively composed finite-time kernels have that convergence under simultaneous convergence of
their strictly ordered time coordinates.  No continuous-time Markov or Hunt property is assumed
or asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace MarkovProcess

noncomputable section







namespace ContinuousPath







end ContinuousPath

section KernelLimits

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [LocallyCompactSpace α]







namespace SubMarkovKernelSemigroup





private theorem finiteDenseApproximation_mem {I : Finset NNReal} (q : I ↪o DenseTime)
    (t : I) :
    DenseTime.castOrderEmbedding (q t) ∈ finiteDenseApproximationPhysicalSet q := by
  rw [finiteDenseApproximationPhysicalSet, denseTimePhysicalSet, Finset.mem_map]
  refine ⟨q t, ?_, rfl⟩
  rw [finiteDenseApproximationIndexSet, Finset.mem_map]
  exact ⟨t, Finset.mem_univ t, rfl⟩



/-- The approximating-set reindexing map is measurable. -/
theorem measurable_finiteDenseApproximationReindex
    {γ : Type*} [MeasurableSpace γ] {I : Finset NNReal} (q : I ↪o DenseTime) :
    Measurable (finiteDenseApproximationReindex (γ := γ) q) := by
  rw [measurable_pi_iff]
  intro t
  let s : finiteDenseApproximationPhysicalSet q :=
    ⟨DenseTime.castOrderEmbedding (q t), finiteDenseApproximation_mem q t⟩
  exact measurable_pi_apply s
end SubMarkovKernelSemigroup
end KernelLimits
end
end MarkovProcess

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Ordered form of finite dense approximations

This file expresses a finite dense-approximation kernel as a finite-time kernel at its
increasing physical times. The final coordinate reindexing is the fixed map
`orderedPathToFiniteSet I`; it does not depend on the chosen dense approximation `q`.

The construction also covers `I = ∅`. In that case the ordered time family and both path
coordinate types are empty.
-/

open MeasureTheory ProbabilityTheory Topology Filter
open scoped NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section





private theorem approximation_mem {I : Finset NNReal} (q : I ↪o DenseTime) (t : I) :
    DenseTime.castOrderEmbedding (q t) ∈ finiteDenseApproximationPhysicalSet q := by
  rw [finiteDenseApproximationPhysicalSet, denseTimePhysicalSet, Finset.mem_map]
  refine ⟨q t, ?_, rfl⟩
  rw [finiteDenseApproximationIndexSet, Finset.mem_map]
  exact ⟨t, Finset.mem_univ t, rfl⟩

private def finiteDenseApproximationOrderEmb {I : Finset NNReal} (q : I ↪o DenseTime) :
    Fin I.card ↪o Fin (finiteDenseApproximationPhysicalSet q).card :=
  (I.orderIsoOfFin rfl).toOrderEmbedding |>.trans
    (OrderEmbedding.ofStrictMono
      (fun t : I => (⟨DenseTime.castOrderEmbedding (q t), approximation_mem q t⟩ :
        finiteDenseApproximationPhysicalSet q))
        (fun _ _ h => DenseTime.castOrderEmbedding.strictMono (q.strictMono h))) |>.trans
    ((finiteDenseApproximationPhysicalSet q).orderIsoOfFin rfl).symm.toOrderEmbedding

private theorem finiteSetTimes_restrict_approximationOrderEmb
    {I : Finset NNReal} (q : I ↪o DenseTime) :
    (finiteSetTimes (finiteDenseApproximationPhysicalSet q)).restrict
        (finiteDenseApproximationOrderEmb q) =
      finiteDenseApproximationOrderedTimes q := by
  apply DFunLike.ext _ _
  intro i
  change finiteSetTimes (finiteDenseApproximationPhysicalSet q)
      (finiteDenseApproximationOrderEmb q i) = _
  simp only [finiteSetTimes, finiteDenseApproximationOrderEmb,
    finiteDenseApproximationOrderedTimes, RelEmbedding.trans_apply]
  exact congrArg Subtype.val
    ((finiteDenseApproximationPhysicalSet q).orderIsoOfFin rfl |>.apply_symm_apply
      ⟨DenseTime.castOrderEmbedding (q (I.orderIsoOfFin rfl i)),
        approximation_mem q (I.orderIsoOfFin rfl i)⟩)

private theorem reindex_comp_orderedPathToFiniteSet
    {gamma : Type*} {I : Finset NNReal} (q : I ↪o DenseTime) :
    finiteDenseApproximationReindex (γ := gamma) q ∘
        orderedPathToFiniteSet (finiteDenseApproximationPhysicalSet q) =
      orderedPathToFiniteSet I ∘
        FiniteOrderedTimes.restrictPath (finiteDenseApproximationOrderEmb q) := by
  funext path t
  simp only [Function.comp_apply, finiteDenseApproximationReindex,
    orderedPathToFiniteSet, FiniteOrderedTimes.restrictPath,
    finiteDenseApproximationOrderEmb, RelEmbedding.trans_apply,
    OrderIso.coe_toOrderEmbedding, OrderIso.apply_symm_apply]
  rfl

/-- A conservative finite dense-approximation kernel is the finite-time kernel at its canonical
ordered physical times, mapped by the fixed, `q`-independent reindexing to `I`-indexed paths.
The statement includes the empty finite set. -/
theorem finiteDenseApproximationKernel_eq_map_finiteTimeKernel
    {alpha : Type*} [MeasurableSpace alpha]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    {I : Finset NNReal} (q : I ↪o DenseTime) :
    finiteDenseApproximationKernel P q =
      (finiteTimeKernel P (finiteDenseApproximationOrderedTimes q)).map
        (orderedPathToFiniteSet I) := by
  rw [finiteDenseApproximationKernel, finiteSetKernel_eq_map, ← Kernel.map_comp_right]
  · rw [reindex_comp_orderedPathToFiniteSet q, Kernel.map_comp_right]
    · rw [hP.finiteTimeKernel_map_restrictPath P,
        finiteSetTimes_restrict_approximationOrderEmb q]
    · exact FiniteOrderedTimes.measurable_restrictPath _
    · exact measurable_orderedPathToFiniteSet _
  · exact measurable_orderedPathToFiniteSet _
  · exact measurable_finiteDenseApproximationReindex q

/-- Coordinatewise convergence of dense approximations gives convergence of each coordinate of
their canonical ordered physical-time families. This is vacuous when `I` is empty. -/
theorem tendsto_finiteDenseApproximationOrderedTimes
    {I : Finset NNReal} (q : ℕ → I ↪o DenseTime)
    (hq : ∀ t, Tendsto (fun k ↦ DenseTime.castOrderEmbedding (q k t)) atTop
      (nhds (t : NNReal))) (i : Fin I.card) :
    Tendsto (fun k ↦ finiteDenseApproximationOrderedTimes (q k) i) atTop
      (nhds (finiteSetTimes I i)) := by
  change Tendsto
    (fun k ↦ DenseTime.castOrderEmbedding (q k (I.orderIsoOfFin rfl i))) atTop
    (nhds ((I.orderIsoOfFin rfl i : I) : NNReal))
  exact hq (I.orderIsoOfFin rfl i)
end
end MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Feller continuity of finite dense approximations

This file proves compact-test convergence of the finite laws obtained by simultaneously
approximating a finite set of nonnegative-real times by dense times. Both the approximating and
limiting kernels are transported through the same ordered-coordinate homeomorphism, after which
the finite-time Feller continuity theorem applies directly.

This is finite-dimensional infrastructure. No path-space Markov property is asserted here; the
Markov and strong Markov statements are in `MarkovProcess/Main.lean`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal CompactlySupported


variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]


theorem solution
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) {I : Finset NNReal} (q : ℕ → I ↪o DenseTime)
    (hq : ∀ t, Tendsto
      (fun k ↦ DenseTime.castOrderEmbedding (q k t)) atTop (nhds (t : NNReal)))
    (f : C_c(I → alpha, ℝ)) (x : alpha) :
    Tendsto
      (fun k ↦ ∫ y, f y ∂finiteDenseApproximationKernel P (q k) x)
      atTop (nhds (∫ y, f y ∂finiteSetKernel P I x)) := by
  have htime : ∀ i, Tendsto
      (fun k ↦ finiteDenseApproximationOrderedTimes (q k) i) atTop
        (nhds (finiteSetTimes I i)) :=
    tendsto_finiteDenseApproximationOrderedTimes q hq
  have h := hFeller.tendsto_integral_compactlySupported_finiteTimeKernel
    hP htime (pullbackFiniteSetCompactTest I f) x
  have happrox (k : ℕ) :
      (∫ y, f y ∂finiteDenseApproximationKernel P (q k) x) =
        ∫ path, pullbackFiniteSetCompactTest I f path
          ∂finiteTimeKernel P (finiteDenseApproximationOrderedTimes (q k)) x := by
    rw [finiteDenseApproximationKernel_eq_map_finiteTimeKernel P hP (q k),
      Kernel.map_apply _ (measurable_orderedPathToFiniteSet I)]
    exact integral_map_orderedPathToFiniteSet I f _
  rw [show (fun k ↦ ∫ y, f y ∂finiteDenseApproximationKernel P (q k) x) =
      (fun k ↦ ∫ path, pullbackFiniteSetCompactTest I f path
        ∂finiteTimeKernel P (finiteDenseApproximationOrderedTimes (q k)) x) from
      funext happrox,
    integral_finiteSetKernel_eq_integral_pullbackFiniteSetCompactTest P I f x]
  exact h
