-- Prove2me | solution 1 for OAI.KadisonKastler.exists_measurable_diagonal_unitary_on_set
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:51:59.362712+00:00
-- url     : https://prove2.me/submissions/97b807af-2e0f-4fc6-9bc0-6a26e0c2e9c0

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K032
import Theorems.Thm_OAI_KadisonKastler_traceHull_mem_ball

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Polar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Polar unitaries close to the identity

We construct the polar factor of an invertible element using the positive
square root supplied by continuous functional calculus.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A : Type*} [CStarAlgebra A]

section Ordered

variable [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Inverting a unit close to one gives the usual geometric-series bound. -/
theorem norm_unit_inv_le_of_near_one [Nontrivial A] (t : Aˣ)
    (ht : ‖(t : A) - 1‖ < 1) :
    ‖((t⁻¹ : Aˣ) : A)‖ ≤ (1 - ‖(t : A) - 1‖)⁻¹ := by
  have hpos : 0 < 1 - ‖(t : A) - 1‖ := sub_pos.mpr ht
  have hidentity : ((t⁻¹ : Aˣ) : A) - 1 =
      ((t⁻¹ : Aˣ) : A) * (1 - (t : A)) := by
    rw [mul_sub, mul_one, Units.inv_mul]
  have htriangle := norm_le_norm_sub_add (((t⁻¹ : Aˣ) : A)) (1 : A)
  have hproduct := norm_mul_le (((t⁻¹ : Aˣ) : A)) (1 - (t : A))
  rw [← hidentity, norm_sub_rev (1 : A) (t : A)] at hproduct
  rw [norm_one] at htriangle
  have hbound : (1 - ‖(t : A) - 1‖) * ‖((t⁻¹ : Aˣ) : A)‖ ≤ 1 := by nlinarith
  simpa only [mul_one] using (le_inv_mul_iff₀ hpos).mpr hbound

/-- A positive unit with upper bounds on its norm and inverse lies within
the same radius of the identity. -/
theorem norm_positive_unit_sub_one_le [Nontrivial A] (s : Aˣ) (hs : 0 ≤ (s : A)) {r : ℝ}
    (hr : 0 ≤ r) (hr₁ : r < 1) (hnorm : ‖(s : A)‖ ≤ 1 + r)
    (hinv : ‖((s⁻¹ : Aˣ) : A)‖ ≤ (1 - r)⁻¹) :
    ‖(s : A) - 1‖ ≤ r := by
  have hrepr : cfc (fun x : ℝ => x - 1) (s : A) = (s : A) - 1 := by
    rw [cfc_sub (fun x : ℝ => x) (fun _ : ℝ => 1) (s : A),
      cfc_id' ℝ (s : A), cfc_const_one ℝ (s : A)]
  rw [← hrepr]
  apply norm_cfc_le hr
  intro x hx
  have hx₀ : 0 ≤ x := spectrum_nonneg_of_nonneg hs hx
  have hxne : x ≠ 0 := by
    intro hzero
    exact spectrum.zero_notMem ℝ s.isUnit (hzero ▸ hx)
  have hxpos : 0 < x := lt_of_le_of_ne hx₀ (Ne.symm hxne)
  have hxupper : x ≤ 1 + r :=
    (Real.le_norm_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans hnorm)
  have hxinv : x⁻¹ ≤ (1 - r)⁻¹ :=
    (Real.le_norm_self (x⁻¹)).trans
      ((spectrum.norm_le_norm_of_mem (spectrum.inv₀_mem_inv hx)).trans hinv)
  have hxlower : 1 - r ≤ x :=
    (inv_le_inv₀ hxpos (sub_pos.mpr hr₁)).mp hxinv
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Taking the absolute value of a unit does not increase its distance from
one, provided that distance is less than one. -/
theorem norm_abs_sub_one_le [Nontrivial A] (t : Aˣ)
    (ht : ‖(t : A) - 1‖ < 1) :
    ‖CFC.abs (t : A) - 1‖ ≤ ‖(t : A) - 1‖ := by
  obtain ⟨u, hu⟩ := exists_unitary_mul_abs t
  let s : Aˣ := (isUnit_abs t).unit
  have hs : (s : A) = CFC.abs (t : A) := (isUnit_abs t).unit_spec
  have hdecomp : (u : A) * (s : A) = (t : A) := by rwa [hs]
  have hinveq : ((s⁻¹ : Aˣ) : A) = ((t⁻¹ : Aˣ) : A) * (u : A) := by
    calc
      ((s⁻¹ : Aˣ) : A) =
          (((t⁻¹ : Aˣ) : A) * (t : A)) * ((s⁻¹ : Aˣ) : A) := by simp
      _ = (((t⁻¹ : Aˣ) : A) * ((u : A) * (s : A))) * ((s⁻¹ : Aˣ) : A) := by
        rw [hdecomp]
      _ = ((t⁻¹ : Aˣ) : A) * (u : A) := by
        simp only [mul_assoc, Units.mul_inv, mul_one]
  have hsinv : ‖((s⁻¹ : Aˣ) : A)‖ = ‖((t⁻¹ : Aˣ) : A)‖ := by
    rw [hinveq, CStarRing.norm_mul_coe_unitary]
  have hsnorm : ‖(s : A)‖ ≤ 1 + ‖(t : A) - 1‖ := by
    rw [hs, CFC.norm_abs]
    have h := norm_le_norm_sub_add (t : A) (1 : A)
    simpa only [norm_one, add_comm] using h
  rw [← hs]
  apply norm_positive_unit_sub_one_le s (by rw [hs]; exact CFC.abs_nonneg _)
    (norm_nonneg _) ht hsnorm
  rw [hsinv]
  exact norm_unit_inv_le_of_near_one t ht

/-- The polar unitary of a unit close to one is within twice that distance
of one. -/
theorem exists_polar_unitary_near_one_of_unit [Nontrivial A] (t : Aˣ)
    (ht : ‖(t : A) - 1‖ < 1) :
    ∃ u : unitary A, (u : A) * CFC.abs (t : A) = (t : A) ∧
      ‖(u : A) - 1‖ ≤ 2 * ‖(t : A) - 1‖ := by
  obtain ⟨u, hu⟩ := exists_unitary_mul_abs t
  refine ⟨u, hu, ?_⟩
  have hdiff : (u : A) - (t : A) = (u : A) * (1 - CFC.abs (t : A)) := by
    rw [mul_sub, mul_one, hu]
  calc
    ‖(u : A) - 1‖ ≤ ‖(u : A) - (t : A)‖ + ‖(t : A) - 1‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖1 - CFC.abs (t : A)‖ + ‖(t : A) - 1‖ := by
      rw [hdiff, CStarRing.norm_coe_unitary_mul]
    _ ≤ ‖(t : A) - 1‖ + ‖(t : A) - 1‖ := by
      apply add_le_add _ le_rfl
      simpa only [norm_sub_rev] using norm_abs_sub_one_le t ht
    _ = 2 * ‖(t : A) - 1‖ := by ring

/-- Every element within distance one of the identity has a unitary polar
factor within twice its original distance of the identity. -/
theorem exists_polar_unitary_near_one (T : A) (hT : ‖T - 1‖ < 1) :
    ∃ u : unitary A, (u : A) * CFC.abs T = T ∧ ‖(u : A) - 1‖ ≤ 2 * ‖T - 1‖ := by
  nontriviality A
  let t : Aˣ := Units.ofNearby 1 T (by simpa using hT)
  have ht : (t : A) = T := rfl
  simpa only [ht] using exists_polar_unitary_near_one_of_unit t (by rwa [ht])

end Ordered

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryIntertwiner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Averaging and polar normalization of a boundary intertwiner

A supplied equivariant bimodule mean gives a near-identity semilinear
intertwiner. Continuous functional calculus passes its transformation law
to the unitary polar factor.
-/

namespace KadisonKastler

open scoped CStarAlgebra BoundedContinuousFunction

noncomputable section

variable {B : Type*} [CStarAlgebra B]

attribute [local instance] OAI.KadisonKastler.boundaryIntertwinerOrder
attribute [local instance] OAI.KadisonKastler.boundaryIntertwinerStarOrder
/-- Left multiplication by a unitary does not change the absolute value. -/
theorem abs_unitary_mul (u : unitary B) (b : B) :
    CFC.abs ((u : B) * b) = CFC.abs b := by
  unfold CFC.abs
  congr 1
  rw [star_mul]
  calc
    star b * star (u : B) * ((u : B) * b) =
        star b * (star (u : B) * (u : B)) * b := by noncomm_ring
    _ = star b * b := by
      rw [Unitary.star_mul_self_of_mem u.property, mul_one]

/-- Right multiplication by a unitary conjugates the absolute value. -/
theorem abs_mul_unitary (b : B) (u : unitary B) :
    CFC.abs (b * (u : B)) = star (u : B) * CFC.abs b * (u : B) := by
  have hm := starAlgHom_map_abs
    (Unitary.conjStarAlgAut ℂ B (star u)).toStarAlgHom b
  have hr : CFC.abs (star (u : B) * b * (u : B)) = CFC.abs (b * (u : B)) := by
    rw [mul_assoc]
    exact abs_unitary_mul (star u) (b * (u : B))
  simpa only [StarAlgEquiv.toStarAlgHom_apply, Unitary.conjStarAlgAut_star_apply, hr]
    using hm.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryDiagonal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.conjugateLinear_one _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.traceFreeCopy_inner _root_.OAI.Generator.Tracial.traceFreeHilbertCoefficient_apply _root_.OAI.Generator.Tracial.traceFreeInclusion_inner _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.TraceQuotientMap.comapEquiv_quotient _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.concreteTraceEmbedding_inner _root_.OAI.KadisonKastler.concreteTraceLeftAction_embedding _root_.OAI.KadisonKastler.concreteTraceLeftUnitary_coe _root_.OAI.KadisonKastler.concreteTraceRightAction_embedding _root_.OAI.KadisonKastler.concreteTraceRightUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.expectedTrace_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrixSequenceQuotient_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.tracialHilbertConjugation_embedding _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonKastler.tracialStarIsometry_embedding _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe _root_.OAI.UltrapowerBridge.quotientMap_smul _root_.OAI.UltrapowerBridge.quotientMap_star _root_.OAI.UltrapowerBridge.quotientTrace_mk _root_.OAI.UltrapowerBridge.quotientTrace_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Pointwise diagonal comparison in a finite algebra

The least-norm argument is carried out in a supplied faithful tracial
Hilbert realization. Bounded completeness of the concrete finite algebra
keeps Hilbert limits in the operator algebra. No measurable selection or
existence of a boundary space is asserted here.
-/

namespace KadisonKastler

open Filter Set
open scoped Topology

noncomputable section

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The least-norm vector of a convex set is unique. -/
theorem eq_of_convex_least_norm {K : Set E} (hK : Convex ℝ K)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K)
    (hxm : ∀ z ∈ K, ‖x‖ ≤ ‖z‖) (hym : ∀ z ∈ K, ‖y‖ ≤ ‖z‖) : x = y := by
  have hn : ‖y‖ = ‖x‖ := le_antisymm (hym x hx) (hxm y hy)
  have hm : (1 / 2 : ℝ) • (x + y) ∈ K := by
    simpa only [smul_add] using hK hx hy (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hp := hxm _ hm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hp
  have hs := mul_self_le_mul_self (norm_nonneg x) hp
  have hpar := parallelogram_law_with_norm_mul ℂ x y
  rw [hn] at hpar
  have hz : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Every nonempty closed convex subset of a Hilbert space has a unique
least-norm vector. -/
theorem exists_unique_least_norm [CompleteSpace E] {K : Set E}
    (hne : K.Nonempty) (hclosed : IsClosed K) (hconvex : Convex ℝ K) :
    ∃! x : E, x ∈ K ∧ ∀ y ∈ K, ‖x‖ ≤ ‖y‖ := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  obtain ⟨x, hx, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    hne hclosed.isComplete hconvex (0 : E)
  have hxm : ∀ y ∈ K, ‖x‖ ≤ ‖y‖ := by
    intro y hy
    have hi : (⨅ w : K, ‖(0 : E) - w‖) ≤ ‖(0 : E) - y‖ :=
      ciInf_le ⟨(0 : ℝ), Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩ (⟨y, hy⟩ : K)
    simpa only [zero_sub, norm_neg] using hmin.le.trans hi
  exact ⟨x, ⟨hx, hxm⟩, fun y hy => eq_of_convex_least_norm hconvex hy.1 hx hy.2 hxm⟩

end Hilbert

section Concrete

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}
variable (J : Algebra M →ₗ[ℂ] E)
variable (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)

/-- The definition agrees with the ordinary Hilbert closed convex hull. -/
theorem diagonalTraceHull_eq (s : Set (Algebra M)) :
    diagonalTraceHull J s = closure (convexHull ℝ (J '' s)) := by
  unfold diagonalTraceHull
  congr 1
  exact (J.restrictScalars ℝ).image_convexHull s

/-- The trace hull is convex. -/
theorem diagonalTraceHull_convex (s : Set (Algebra M)) :
    Convex ℝ (diagonalTraceHull J s) := by
  rw [diagonalTraceHull_eq]
  exact (convex_convexHull ℝ _).closure

include hJ in
/-- A nonempty family of contractions near one has an actual unique
least-two-norm operator in its trace Hilbert closed convex hull. -/
theorem exists_unique_diagonal_least [CompleteSpace E]
    (hτ : FiniteVectorTrace τ) {s : Set (Algebra M)} (hsne : s.Nonempty)
    {r : ℝ} (hr : 0 ≤ r) (hs1 : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hsr : ∀ x ∈ s, ‖x - 1‖ ≤ r) :
    ∃! b : Algebra M, J b ∈ diagonalTraceHull J s ∧ ‖b‖ ≤ 1 ∧ ‖b - 1‖ ≤ r ∧
      ∀ z ∈ diagonalTraceHull J s, ‖J b‖ ≤ ‖z‖ := by
  obtain ⟨z, hz, hzu⟩ := exists_unique_least_norm
    (show (diagonalTraceHull J s).Nonempty from by
      obtain ⟨x, hx⟩ := hsne
      exact ⟨J x, subset_closure ⟨x, subset_convexHull ℝ s hx, rfl⟩⟩)
    isClosed_closure (diagonalTraceHull_convex J s)
  obtain ⟨b, hbz, hbr⟩ := traceHull_mem_ball J hJ hτ 1 hr hsr hz.1
  obtain ⟨c, hcz, hc1⟩ := traceHull_mem_ball J hJ hτ 0 (r := 1) (by norm_num)
    (fun x hx => by simpa only [sub_zero] using hs1 x hx) hz.1
  have hbc : b = c := traceHilbert_injective J hJ (hbz.trans hcz.symm)
  have hb1 : ‖b‖ ≤ 1 := by simpa only [hbc, sub_zero] using hc1
  refine ⟨b, ⟨hbz ▸ hz.1, hb1, hbr, hbz ▸ hz.2⟩, ?_⟩
  intro c hc
  apply traceHilbert_injective J hJ
  exact (hzu (J c) ⟨hc.1, hc.2.2.2⟩).trans hbz.symm


include hJ in
/-- Trace-isometric linear maps carry trace convex hulls into the hull of
any containing image of the generators. -/
theorem traceHull_map (F : Algebra M →ₗ[ℂ] Algebra M)
    (hF : ∀ x, traceTwoNorm τ (F x) = traceTwoNorm τ x)
    {s t : Set (Algebra M)} (himage : F '' s ⊆ t)
    {b : Algebra M} (hb : J b ∈ diagonalTraceHull J s) :
    J (F b) ∈ diagonalTraceHull J t := by
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp hb
  choose x hxmem hx using hv
  apply isClosed_closure.mem_of_tendsto
    (show Tendsto (fun n => J (F (x n))) atTop (𝓝 (J (F b))) from ?_)
    (Eventually.of_forall fun n => subset_closure ?_)
  · rw [← tendsto_sub_nhds_zero_iff]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hn := (hvlim.sub_const (J b)).norm
    simpa only [sub_self, norm_zero, ← hx, ← map_sub, hJ, hF] using hn
  · refine ⟨F (x n), ?_, rfl⟩
    apply convexHull_mono himage
    have hm : F (x n) ∈ F '' convexHull ℝ s := ⟨x n, hxmem n, rfl⟩
    have heq : F '' convexHull ℝ s = convexHull ℝ (F '' s) :=
      (F.restrictScalars ℝ).image_convexHull s
    rwa [heq] at hm

include hJ in
/-- Least vectors transform exactly under left and right unitary actions,
provided these actions identify the two generating sets. -/
theorem diagonal_least_covariance (u v : unitary (Algebra M))
    {s t : Set (Algebra M)}
    (hforward : ∀ x ∈ s, (u : Algebra M) * x * star (v : Algebra M) ∈ t)
    (hbackward : ∀ y ∈ t, star (u : Algebra M) * y * (v : Algebra M) ∈ s)
    {b c : Algebra M}
    (hb : J b ∈ diagonalTraceHull J s)
    (hc : J c ∈ diagonalTraceHull J t)
    (hbm : ∀ z ∈ diagonalTraceHull J s, ‖J b‖ ≤ ‖z‖)
    (hcm : ∀ z ∈ diagonalTraceHull J t, ‖J c‖ ≤ ‖z‖) :
    c = (u : Algebra M) * b * star (v : Algebra M) := by
  let F := LinearMap.mulLeftRight ℂ ((u : Algebra M), star (v : Algebra M))
  let R := LinearMap.mulLeftRight ℂ (star (u : Algebra M), (v : Algebra M))
  have hF (x : Algebra M) : traceTwoNorm τ (F x) = traceTwoNorm τ x := by
    change traceTwoNorm τ (((u : Algebra M) * x) * (star v : unitary (Algebra M))) = _
    simp only [traceTwoNorm_mul_unitary, traceTwoNorm_unitary_mul]
  have hR (x : Algebra M) : traceTwoNorm τ (R x) = traceTwoNorm τ x := by
    change traceTwoNorm τ (((star u : unitary (Algebra M)) : Algebra M) * x *
      (v : Algebra M)) = _
    simp only [traceTwoNorm_mul_unitary, traceTwoNorm_unitary_mul]
  have hFb := traceHull_map J hJ F hF (by rintro _ ⟨x, hx, rfl⟩; exact hforward x hx) hb
  have hRc := traceHull_map J hJ R hR (by rintro _ ⟨x, hx, rfl⟩; exact hbackward x hx) hc
  have hle : ‖J (F b)‖ ≤ ‖J c‖ := by
    simpa only [hJ, hF, hR] using hbm _ hRc
  apply traceHilbert_injective J hJ
  exact eq_of_convex_least_norm (diagonalTraceHull_convex J t) hc hFb hcm
    (fun z hz => hle.trans (hcm z hz))


end Concrete


section Polar

variable {B : Type*} [CStarAlgebra B]

attribute [local instance] OAI.KadisonKastler.boundaryDiagonalOrder
attribute [local instance] OAI.KadisonKastler.boundaryDiagonalStarOrder
/-- Polar normalization respects left and right multiplication by
unitaries, for invertible elements. -/
theorem polar_unitary_sandwich {b c : B} (hbunit : IsUnit b)
    (u v a d : unitary B) (ha : (a : B) * CFC.abs b = b)
    (hd : (d : B) * CFC.abs c = c)
    (hbc : b = (u : B) * c * star (v : B)) :
    (a : B) = (u : B) * (d : B) * star (v : B) := by
  have habs : CFC.abs b = (v : B) * CFC.abs c * star (v : B) := by
    rw [hbc, mul_assoc, abs_unitary_mul]
    simpa only [Unitary.coe_star, star_star] using abs_mul_unitary c (star v)
  have hi : IsUnit (CFC.abs b) := by
    obtain ⟨t, rfl⟩ := hbunit
    exact isUnit_abs t
  apply hi.mul_right_cancel
  rw [ha, habs]
  calc
    b = (u : B) * ((d : B) * CFC.abs c) * star (v : B) := by rw [hd, hbc]
    _ = ((u : B) * (d : B) * star (v : B)) *
        ((v : B) * CFC.abs c * star (v : B)) := by
      symm
      calc
        _ = (u : B) * (d : B) * (star (v : B) * (v : B)) * CFC.abs c * star (v : B) := by
          noncomm_ring
        _ = _ := by
          rw [Unitary.star_mul_self_of_mem v.property, mul_one]
          noncomm_ring

end Polar


end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryDiagonalMeasurable
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurability of diagonal least-norm vectors

Finite rational convex expressions form a countable dense subset of each
closed convex hull. Choosing the first expression within a specified
squared-norm tolerance gives measurable approximants; the parallelogram
identity forces their convergence to the unique least vector.
-/

namespace KadisonKastler

open Filter Set MeasureTheory TopologicalSpace
open scoped Topology

noncomputable section

private theorem convexParameter_nonneg (t : ℝ) : 0 ≤ convexParameter t := le_max_left _ _
private theorem convexParameter_le_one (t : ℝ) : convexParameter t ≤ 1 := by
  exact max_le (by norm_num) (min_le_left _ _)
private theorem convexParameter_eq {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    convexParameter t = t := by simp [convexParameter, min_eq_right h1, max_eq_right h0]

namespace RationalConvexExpr

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every expression belongs to the ordinary convex hull of its leaves. -/
theorem eval_mem_convexHull (v : ι → E) (a : RationalConvexExpr ι) :
    eval v a ∈ convexHull ℝ (Set.range v) := by
  induction a with
  | leaf i => exact subset_convexHull ℝ _ ⟨i, rfl⟩
  | blend q a b ha hb =>
    exact convex_convexHull ℝ _ ha hb (convexParameter_nonneg _)
      (sub_nonneg.mpr (convexParameter_le_one _)) (add_sub_cancel _ _)

/-- The closure of rational combinations is closed under all real convex
combinations, by density of the rational parameters. -/
theorem convex_closure_range_eval (v : ι → E) :
    Convex ℝ (closure (Set.range (eval v))) := by
  intro x hx y hy a b ha hb hab
  have hq (q : ℚ) : convexParameter (q : ℝ) • x +
      (1 - convexParameter (q : ℝ)) • y ∈ closure (Set.range (eval v)) := by
    apply map_mem_closure₂ (f := fun x y : E =>
      convexParameter (q : ℝ) • x + (1 - convexParameter (q : ℝ)) • y)
      (by fun_prop) hx hy
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨blend q c d, rfl⟩
  have hcont : Continuous (fun t : ℝ => convexParameter t • x +
      (1 - convexParameter t) • y) := by unfold convexParameter; fun_prop
  have hmem := map_mem_closure hcont (Rat.denseRange_cast a) (by
    rintro _ ⟨q, rfl⟩
    exact hq q)
  rw [isClosed_closure.closure_eq] at hmem
  have ha1 : a ≤ 1 := by linarith
  simpa only [convexParameter_eq ha ha1, show 1 - a = b by linarith] using hmem

/-- Rational convex expressions are dense in the real convex hull. -/
theorem closure_range_eval (v : ι → E) :
    closure (Set.range (eval v)) = closure (convexHull ℝ (Set.range v)) := by
  apply le_antisymm
  · exact closure_mono (Set.range_subset_iff.mpr (eval_mem_convexHull v))
  · apply closure_minimal _ isClosed_closure
    apply convexHull_min _ (convex_closure_range_eval v)
    rintro _ ⟨i, rfl⟩
    exact subset_closure ⟨leaf i, rfl⟩

/-- Evaluation preserves strong measurability of a family of leaves. -/
theorem stronglyMeasurable_eval {P : Type*} [MeasurableSpace P]
    (v : ι → P → E) (hv : ∀ i, StronglyMeasurable (v i)) (a : RationalConvexExpr ι) :
    StronglyMeasurable (fun p => eval (fun i => v i p) a) := by
  induction a with
  | leaf i => exact hv i
  | blend q a b ha hb => exact (ha.const_smul _).add (hb.const_smul _)

end RationalConvexExpr

section Least

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A squared-norm tolerance controls distance to a least vector. -/
theorem norm_sub_sq_le_twice_gap {K : Set E} (hK : Convex ℝ K)
    {c z : E} (hc : c ∈ K) (hz : z ∈ K) (hmin : ∀ y ∈ K, ‖c‖ ≤ ‖y‖) :
    ‖z - c‖ ^ 2 ≤ 2 * (‖z‖ ^ 2 - ‖c‖ ^ 2) := by
  have hm : (1 / 2 : ℝ) • (z + c) ∈ K := by
    simpa only [smul_add] using hK hz hc (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hp := hmin _ hm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hp
  have hs := mul_self_le_mul_self (norm_nonneg c) hp
  have hpar := parallelogram_law_with_norm ℂ z c
  nlinarith

omit [InnerProductSpace ℂ E] in
/-- The infimum over a dense countable family is the least squared norm. -/
theorem iInf_norm_sq_eq_least (z : ℕ → E) (c : E)
    (hc : c ∈ closure (Set.range z))
    (hmin : ∀ y ∈ closure (Set.range z), ‖c‖ ≤ ‖y‖) :
    (⨅ n, ‖z n‖ ^ 2) = ‖c‖ ^ 2 := by
  have hlo : ‖c‖ ^ 2 ≤ ⨅ n, ‖z n‖ ^ 2 := by
    apply le_ciInf
    intro n
    exact pow_le_pow_left₀ (norm_nonneg c) (hmin _ (subset_closure ⟨n, rfl⟩)) _
  obtain ⟨w, hw, hwlim⟩ := mem_closure_iff_seq_limit.mp hc
  have hi (n : ℕ) : (⨅ n, ‖z n‖ ^ 2) ≤ ‖w n‖ ^ 2 := by
    obtain ⟨k, hk⟩ := hw n
    rw [← hk]
    exact ciInf_le ⟨0, Set.forall_mem_range.mpr (fun _ => sq_nonneg _)⟩ k
  exact le_antisymm (ge_of_tendsto (hwlim.norm.pow 2) (Eventually.of_forall hi)) hlo

variable {P : Type*} [MeasurableSpace P] [MeasurableSpace E] [BorelSpace E]
  [SeparableSpace E]

/-- The first countable approximant with almost least squared norm is a
measurable function; its limit is the least vector. -/
theorem stronglyMeasurable_countable_least (z : ℕ → P → E)
    (hz : ∀ n, StronglyMeasurable (z n)) (c : P → E)
    (hc : ∀ p, c p ∈ closure (Set.range (fun n => z n p)))
    (hconv : ∀ p, Convex ℝ (closure (Set.range (fun n => z n p))))
    (hmin : ∀ p y, y ∈ closure (Set.range (fun n => z n p)) → ‖c p‖ ≤ ‖y‖) :
    StronglyMeasurable c := by
  let d : P → ℝ := fun p => ⨅ n, ‖z n p‖ ^ 2
  have hd : Measurable d := Measurable.iInf (fun n => (hz n).measurable.norm.pow_const 2)
  have hdeq (p : P) : d p = ‖c p‖ ^ 2 := iInf_norm_sq_eq_least _ _ (hc p) (hmin p)
  have hex (k : ℕ) (p : P) : ∃ n, ‖z n p‖ ^ 2 < d p + 1 / ((k : ℝ) + 1) := by
    apply exists_lt_of_ciInf_lt
    have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
    exact lt_add_of_pos_right _ hpos
  let a : ℕ → P → E := fun k p => z (Nat.find (hex k p)) p
  have ham (k : ℕ) : StronglyMeasurable (a k) := by
    apply Measurable.stronglyMeasurable
    exact Measurable.find (fun n => (hz n).measurable)
      (fun n => measurableSet_lt ((hz n).measurable.norm.pow_const 2)
        (hd.add_const _)) (hex k)
  apply stronglyMeasurable_of_tendsto atTop ham
  apply tendsto_pi_nhds.mpr
  intro p
  rw [← tendsto_sub_nhds_zero_iff]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hbound (k : ℕ) : ‖a k p - c p‖ ≤ Real.sqrt (2 / ((k : ℝ) + 1)) := by
    have hgap := norm_sub_sq_le_twice_gap (hconv p) (hc p)
      (subset_closure ⟨Nat.find (hex k p), rfl⟩) (hmin p)
    have hk := Nat.find_spec (hex k p)
    have hk' : ‖a k p‖ ^ 2 < ‖c p‖ ^ 2 + 1 / ((k : ℝ) + 1) :=
      hk.trans_le (by rw [hdeq p])
    change ‖a k p - c p‖ ^ 2 ≤ 2 * (‖a k p‖ ^ 2 - ‖c p‖ ^ 2) at hgap
    have hs : ‖a k p - c p‖ ^ 2 ≤ 2 / ((k : ℝ) + 1) := calc
      _ ≤ 2 * (‖a k p‖ ^ 2 - ‖c p‖ ^ 2) := hgap
      _ ≤ 2 * (1 / ((k : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hk']) (by norm_num)
      _ = _ := by ring
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hs
  apply squeeze_zero (fun _ => norm_nonneg _) hbound
  have ht : Tendsto (fun k : ℕ => 2 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp ht


/-- The least vector of the closed convex hull of countably many strongly
measurable Hilbert-valued fields is strongly measurable. -/
theorem stronglyMeasurable_convex_least {ι : Type*} [Countable ι] [Nonempty ι]
    (v : ι → P → E) (hv : ∀ i, StronglyMeasurable (v i)) (c : P → E)
    (hc : ∀ p, c p ∈ closure (convexHull ℝ (Set.range (fun i => v i p))))
    (hmin : ∀ p y, y ∈ closure (convexHull ℝ (Set.range (fun i => v i p))) →
      ‖c p‖ ≤ ‖y‖) : StronglyMeasurable c := by
  let : Nonempty (RationalConvexExpr ι) := ⟨.leaf (Classical.choice inferInstance)⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (RationalConvexExpr ι)
  let z : ℕ → P → E := fun n p => RationalConvexExpr.eval (fun i => v i p) (e n)
  have hclosure (p : P) : closure (Set.range (fun n => z n p)) =
      closure (convexHull ℝ (Set.range (fun i => v i p))) := by
    have hrange : Set.range (fun n => z n p) =
        Set.range (RationalConvexExpr.eval (fun i => v i p)) :=
      he.range_comp _
    rw [hrange, RationalConvexExpr.closure_range_eval]
  apply stronglyMeasurable_countable_least z
    (fun n => RationalConvexExpr.stronglyMeasurable_eval v hv (e n)) c
  · intro p
    rw [hclosure]
    exact hc p
  · intro p
    rw [hclosure]
    exact (convex_convexHull ℝ _).closure
  · intro p y hy
    rw [hclosure] at hy
    exact hmin p y hy

/-- Almost-everywhere measurable generators suffice: choose measurable
versions of the leaves, apply the explicit countable approximation, and
use uniqueness on the common conull set. -/
theorem aestronglyMeasurable_convex_least [CompleteSpace E]
    {ι : Type*} [Countable ι] [Nonempty ι] {μ : Measure P}
    (v : ι → P → E) (hv : ∀ i, AEStronglyMeasurable (v i) μ) (c : P → E)
    (hc : ∀ p, c p ∈ closure (convexHull ℝ (Set.range (fun i => v i p))))
    (hmin : ∀ p y, y ∈ closure (convexHull ℝ (Set.range (fun i => v i p))) →
      ‖c p‖ ≤ ‖y‖) : AEStronglyMeasurable c μ := by
  let v' : ι → P → E := fun i => (hv i).mk (v i)
  have hex (p : P) : ∃ x : E,
      x ∈ closure (convexHull ℝ (Set.range (fun i => v' i p))) ∧
      ∀ y ∈ closure (convexHull ℝ (Set.range (fun i => v' i p))), ‖x‖ ≤ ‖y‖ := by
    apply (exists_unique_least_norm ?_ isClosed_closure (convex_convexHull ℝ _).closure).exists
    exact ⟨v' (Classical.choice inferInstance) p,
      subset_closure (subset_convexHull ℝ _ (Set.mem_range_self _))⟩
  choose c' hc' using hex
  have hcm : StronglyMeasurable c' := stronglyMeasurable_convex_least v'
    (fun i => (hv i).stronglyMeasurable_mk) c' (fun p => (hc' p).1) (fun p => (hc' p).2)
  apply hcm.aestronglyMeasurable.congr
  filter_upwards [ae_all_iff.mpr (fun i => (hv i).ae_eq_mk)] with p hp
  have heq : (fun i => v i p) = fun i => v' i p := funext hp
  apply eq_of_convex_least_norm (convex_convexHull ℝ _).closure (hc' p).1
    (by simpa only [heq] using hc p) (hc' p).2
  intro y hy
  exact hmin p y (by simpa only [heq] using hy)

end Least

/-- Measurability of the actual diagonal least operator in its supplied
separable trace Hilbert realization. -/
theorem aestronglyMeasurable_diagonal_least
    {H E P ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace P] [Countable ι] [Nonempty ι]
    {M : VonNeumannAlgebra H} (J : Algebra M →ₗ[ℂ] E) {μ : Measure P}
    (v : ι → P → Algebra M)
    (hv : ∀ i, AEStronglyMeasurable (fun p => J (v i p)) μ)
    (c : P → Algebra M)
    (hc : ∀ p, J (c p) ∈ diagonalTraceHull J (Set.range (fun i => v i p)))
    (hmin : ∀ p y, y ∈ diagonalTraceHull J (Set.range (fun i => v i p)) →
      ‖J (c p)‖ ≤ ‖y‖) : AEStronglyMeasurable (fun p => J (c p)) μ := by
  apply aestronglyMeasurable_convex_least (fun i p => J (v i p)) hv (fun p => J (c p))
  · intro p
    simpa only [diagonalTraceHull_eq, ← Set.range_comp, Function.comp_def] using hc p
  · intro p y hy
    apply hmin p y
    simpa only [diagonalTraceHull_eq, ← Set.range_comp, Function.comp_def] using hy



end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryPolarTrace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.TraceQuotientMap.comapEquiv_quotient _root_.OAI.KadisonKastler.concreteTraceEmbedding_inner _root_.OAI.KadisonKastler.expectedTrace_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixSequenceQuotient_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.tracialHilbertConjugation_embedding _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonKastler.tracialStarIsometry_embedding _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Tracial continuity of the near-identity polar factor

The proof uses the trace pairing and the norm bound on each positive
polar factor. It does not require a measurable functional-calculus
selection or an operator-topology continuity theorem.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B]

/-- In a tracial state, taking the adjoint of one factor does not change
the real pairing with a selfadjoint factor. -/
theorem FaithfulTracialState.re_star_mul_selfAdjoint (τ : FaithfulTracialState B)
    (y p : B) (hp : IsSelfAdjoint p) :
    (τ.toLinearMap (star y * p)).re = (τ.toLinearMap (y * p)).re := by
  calc
    _ = (τ.toLinearMap (p * star y)).re := congrArg Complex.re (τ.tracial _ _)
    _ = (τ.toLinearMap (star (y * p))).re := by rw [star_mul, hp.star_eq]
    _ = (star (τ.toLinearMap (y * p))).re := by rw [τ.map_star]
    _ = _ := by simp

/-- A trace estimate for one bounded right factor. -/
theorem FaithfulTracialState.norm_square_pairing_le (τ : FaithfulTracialState B)
    (x d : B) : ‖τ.toLinearMap (star x * x * d)‖ ≤ ‖d‖ * traceTwoNorm τ x ^ 2 := by
  calc
    _ = ‖τ.toLinearMap (star x * (x * d))‖ := by rw [mul_assoc]
    _ ≤ traceTwoNorm τ x * traceTwoNorm τ (x * d) := τ.cauchySchwarz x (x * d)
    _ ≤ traceTwoNorm τ x * (traceTwoNorm τ x * ‖d‖) :=
      mul_le_mul_of_nonneg_left (traceTwoNorm_mul_le_right τ x d) (traceTwoNorm_nonneg τ x)
    _ = _ := by ring

/-- Exact real trace identity underlying the polar Lipschitz estimate. -/
theorem polar_trace_pairing_identity (τ : FaithfulTracialState B)
    (u v : unitary B) (p q : B) (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q) :
    2 * (τ.toLinearMap (star ((u : B) - (v : B)) * ((u : B) * p - (v : B) * q))).re =
      (τ.toLinearMap (star ((u : B) - (v : B)) * ((u : B) - (v : B)) * (p + q))).re := by
  have he1 : star ((u : B) - (v : B)) * ((u : B) * p - (v : B) * q) =
      p + q - star (u : B) * (v : B) * q - star (v : B) * (u : B) * p := by
    calc
      _ = (star (u : B) * (u : B)) * p + (star (v : B) * (v : B)) * q -
          star (u : B) * (v : B) * q - star (v : B) * (u : B) * p := by
        rw [star_sub]
        noncomm_ring
      _ = _ := by rw [Unitary.star_mul_self_of_mem u.property,
        Unitary.star_mul_self_of_mem v.property, one_mul, one_mul]
  have he2 : star ((u : B) - (v : B)) * ((u : B) - (v : B)) * (p + q) =
      p + q + p + q - star (u : B) * (v : B) * p - star (u : B) * (v : B) * q -
        star (v : B) * (u : B) * p - star (v : B) * (u : B) * q := by
    calc
      _ = (star (u : B) * (u : B)) * (p + q) +
          (star (v : B) * (v : B)) * (p + q) -
          star (u : B) * (v : B) * p - star (u : B) * (v : B) * q -
          star (v : B) * (u : B) * p - star (v : B) * (u : B) * q := by
        rw [star_sub]
        noncomm_ring
      _ = _ := by
        simp only [Unitary.star_mul_self_of_mem u.property,
          Unitary.star_mul_self_of_mem v.property, one_mul]
        noncomm_ring
  have hsp := τ.re_star_mul_selfAdjoint (star (v : B) * (u : B)) p hp
  have hsq := τ.re_star_mul_selfAdjoint (star (v : B) * (u : B)) q hq
  simp only [star_mul, star_star] at hsp hsq
  rw [he1, he2]
  simp only [map_add, map_sub, Complex.add_re, Complex.sub_re]
  linarith

/-- Positive polar factors within radius `r` of one give a tracial
Lipschitz bound, with no commutation requirement between the factors. -/
theorem polar_traceTwoNorm_bound_of_factors (τ : FaithfulTracialState B)
    (u v : unitary B) (p q : B) (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q)
    {r : ℝ} (hpn : ‖p - 1‖ ≤ r) (hqn : ‖q - 1‖ ≤ r) :
    (1 - r) * traceTwoNorm τ ((u : B) - (v : B)) ≤
      traceTwoNorm τ ((u : B) * p - (v : B) * q) := by
  let x : B := (u : B) - (v : B)
  let e : B := (u : B) * p - (v : B) * q
  change (1 - r) * traceTwoNorm τ x ≤ traceTwoNorm τ e
  have hpair := polar_trace_pairing_identity τ u v p q hp hq
  change 2 * (τ.toLinearMap (star x * e)).re =
    (τ.toLinearMap (star x * x * (p + q))).re at hpair
  have hdecomp : star x * x * (p + q) = star x * x + star x * x +
      star x * x * (p - 1) + star x * x * (q - 1) := by noncomm_ring
  rw [hdecomp, map_add, map_add, map_add, Complex.add_re, Complex.add_re,
    Complex.add_re, ← traceTwoNorm_sq τ x] at hpair
  have hlow (d : B) (hd : ‖d‖ ≤ r) :
      -r * traceTwoNorm τ x ^ 2 ≤ (τ.toLinearMap (star x * x * d)).re := by
    have hn := (τ.norm_square_pairing_le x d).trans
      (mul_le_mul_of_nonneg_right hd (sq_nonneg _))
    have hl := (abs_le.mp (Complex.abs_re_le_norm (τ.toLinearMap (star x * x * d)))).1
    linarith
  have hlp := hlow (p - 1) hpn
  have hlq := hlow (q - 1) hqn
  have hl : (1 - r) * traceTwoNorm τ x ^ 2 ≤ (τ.toLinearMap (star x * e)).re := by
    nlinarith
  have hu := (Complex.re_le_norm (τ.toLinearMap (star x * e))).trans (τ.cauchySchwarz x e)
  have hn := traceTwoNorm_nonneg τ x
  by_cases hx : traceTwoNorm τ x = 0
  · simpa only [hx, mul_zero] using traceTwoNorm_nonneg τ e
  · have hxpos : 0 < traceTwoNorm τ x := lt_of_le_of_ne hn (Ne.symm hx)
    have hmul : traceTwoNorm τ x * ((1 - r) * traceTwoNorm τ x) ≤
        traceTwoNorm τ x * traceTwoNorm τ e := by nlinarith
    exact (mul_le_mul_iff_right₀ hxpos).mp hmul

attribute [local instance] OAI.KadisonKastler.boundaryPolarTraceOrder
attribute [local instance] OAI.KadisonKastler.boundaryPolarTraceStarOrder
/-- Near-identity unitary polar factors are Lipschitz for the faithful
tracial two-norm. -/
theorem polar_traceTwoNorm_lipschitz (τ : FaithfulTracialState B)
    (b c : B) (u v : unitary B)
    (hu : (u : B) * CFC.abs b = b) (hv : (v : B) * CFC.abs c = c)
    {r : ℝ} (hr : r < 1) (hb : ‖b - 1‖ ≤ r) (hc : ‖c - 1‖ ≤ r) :
    (1 - r) * traceTwoNorm τ ((u : B) - (v : B)) ≤ traceTwoNorm τ (b - c) := by
  have h10 : (1 : B) ≠ 0 := by
    intro h
    have hm := τ.map_one
    rw [h, map_zero] at hm
    exact zero_ne_one hm
  let : Nontrivial B := ⟨⟨1, 0, h10⟩⟩
  have hab (x : B) (hx : ‖x - 1‖ ≤ r) : ‖CFC.abs x - 1‖ ≤ r := by
    let t : Bˣ := Units.ofNearby 1 x (by simpa using hx.trans_lt hr)
    exact (norm_abs_sub_one_le t (by exact hx.trans_lt hr)).trans hx
  have h := polar_traceTwoNorm_bound_of_factors τ u v (CFC.abs b) (CFC.abs c)
    (CFC.abs_nonneg b).isSelfAdjoint (CFC.abs_nonneg c).isSelfAdjoint (hab b hb) (hab c hc)
  simpa only [hu, hv] using h


/-- The explicit Lipschitz constant on a fixed neighborhood of one. -/
theorem polar_traceTwoNorm_le_inv_mul (τ : FaithfulTracialState B)
    (b c : B) (u v : unitary B)
    (hu : (u : B) * CFC.abs b = b) (hv : (v : B) * CFC.abs c = c)
    {r : ℝ} (hr : r < 1) (hb : ‖b - 1‖ ≤ r) (hc : ‖c - 1‖ ≤ r) :
    traceTwoNorm τ ((u : B) - (v : B)) ≤ (1 - r)⁻¹ * traceTwoNorm τ (b - c) := by
  have h := polar_traceTwoNorm_lipschitz τ b c u v hu hv hr hb hc
  calc
    _ ≤ traceTwoNorm τ (b - c) / (1 - r) :=
      (le_div_iff₀ (sub_pos.mpr hr)).mpr (by simpa only [mul_comm] using h)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryPolarMeasurable
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instTopologicalSpaceElemProdForallNatStrongUnitarySpace _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurability of the diagonal unitary polar field

The polar factor is a Lipschitz function of a near-identity operator in
its tracial Hilbert realization. Factoring through the range of the
measurable least field therefore supplies its measurability.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace Set

noncomputable section

section Polar

variable {B E P : Type*} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [SeparableSpace E] [MeasurableSpace P]

attribute [local instance] OAI.KadisonKastler.boundaryPolarMeasurableOrder
attribute [local instance] OAI.KadisonKastler.boundaryPolarMeasurableStarOrder
/-- A uniformly near-identity field has measurable unitary polar factors
whenever the original field is measurable in its tracial Hilbert space. -/
theorem aestronglyMeasurable_polar_trace
    (τ : FaithfulTracialState B) (J : B →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) {μ : Measure P}
    (c : P → B) (a : P → unitary B) {r : ℝ} (hr : r < 1)
    (hnear : ∀ p, ‖c p - 1‖ ≤ r)
    (hpolar : ∀ p, (a p : B) * CFC.abs (c p) = c p)
    (hmeas : AEStronglyMeasurable (fun p => J (c p)) μ) :
    AEStronglyMeasurable (fun p => J (a p : B)) μ := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let K : ℝ := (1 - r)⁻¹
  have hK : 0 ≤ K := inv_nonneg.mpr (sub_pos.mpr hr).le
  have hpair (p q : P) : ‖J (a p : B) - J (a q : B)‖ ≤
      K * ‖J (c p) - J (c q)‖ := by
    simpa only [← map_sub, hJ] using
      polar_traceTwoNorm_le_inv_mul τ (c p) (c q) (a p) (a q)
        (hpolar p) (hpolar q) hr (hnear p) (hnear q)
  let S : Set E := Set.range (fun p => J (c p))
  have hrep (z : S) : ∃ p : P, J (c p) = z.val := z.property
  choose rep hrep using hrep
  let F : S → E := fun z => J (a (rep z) : B)
  have hF : LipschitzWith ⟨K, hK⟩ F := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    change dist (F z) (F w) ≤ K * dist z w
    have h := hpair (rep z) (rep w)
    simpa only [F, hrep, Subtype.dist_eq, dist_eq_norm] using h
  let f : P → S := fun p => ⟨J (c p), Set.mem_range_self p⟩
  have hf : AEMeasurable f μ := hmeas.aemeasurable.subtype_mk
  have hFm : AEStronglyMeasurable (fun p => F (f p)) μ :=
    (hF.continuous.measurable.comp_aemeasurable hf).aestronglyMeasurable
  apply hFm.congr
  exact Filter.Eventually.of_forall fun p => by
    have h := hpair (rep (f p)) p
    rw [hrep] at h
    change ‖F (f p) - J (a p : B)‖ ≤ K * ‖J (c p) - J (c p)‖ at h
    rw [sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

end Polar

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AEBoundaryDiagonal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.TraceQuotientMap.comapEquiv_quotient _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.expectedTrace_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrixSequenceQuotient_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Diagonal comparison from almost-everywhere cocycle data

A countable group has a common invariant conull set for the cocycle laws
and approximation bounds. Outside that set the generating family is filled
with one good value. This provides global bounds for the least-vector and
polar constructions; covariance is required only on the conull set.
-/

namespace KadisonKastler

open MeasureTheory Filter TopologicalSpace

noncomputable section

section Local

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [SeparableSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}

attribute [local instance] OAI.KadisonKastler.aeDiagonalOrder
local instance aeDiagonalStarOrder : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

/-- Global boundedness suffices for the measurable least field. The
cocycle laws need hold only on the set where covariance is asserted. -/
theorem exists_measurable_diagonal_unitary_on_set_oai
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ)
    {G D : Type*} [Group G] [Countable G] [MeasurableSpace D] {μ : Measure (D × D)}
    (S : Set D) (shift : G → D → D) (W : G → D → unitary (Algebra M))
    (hW : ∀ g t x, x ∈ S → (W (g * t) x : Algebra M) =
      (W g x : Algebra M) * (W t (shift g x) : Algebra M))
    (hWmeas : ∀ t, AEStronglyMeasurable
      (fun p : D × D => J ((W t p.1 : Algebra M) * star (W t p.2 : Algebra M))) μ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hnear : ∀ t x y, ‖(W t x : Algebra M) * star (W t y : Algebra M) - 1‖ ≤ r) :
    ∃ a : D → D → unitary (Algebra M),
      AEStronglyMeasurable (fun p : D × D => J (a p.1 p.2 : Algebra M)) μ ∧
      (∀ x y, ‖(a x y : Algebra M) - 1‖ ≤ 2 * r) ∧
      (∀ g x y, x ∈ S → y ∈ S → (a x y : Algebra M) =
        (W g x : Algebra M) * (a (shift g x) (shift g y) : Algebra M) *
          star (W g y : Algebra M)) := by
  have hex (x y : D) : ∃ b : Algebra M,
      J b ∈ diagonalTraceHull J (diagonalGenerators W x y) ∧ ‖b‖ ≤ 1 ∧
        ‖b - 1‖ ≤ r ∧
        ∀ z ∈ diagonalTraceHull J (diagonalGenerators W x y), ‖J b‖ ≤ ‖z‖ := by
    apply (exists_unique_diagonal_least J hJ hτ (Set.range_nonempty _) hr0 ?_ ?_).exists
    · rintro _ ⟨t, rfl⟩
      simpa only [Submonoid.coe_mul, Unitary.coe_star] using
        norm_unitary_le_one (W t x * star (W t y))
    · rintro _ ⟨t, rfl⟩
      exact hnear t x y
  choose c hc using hex
  have hcm : AEStronglyMeasurable (fun p : D × D => J (c p.1 p.2)) μ :=
    aestronglyMeasurable_diagonal_least J
      (fun t (p : D × D) => (W t p.1 : Algebra M) * star (W t p.2 : Algebra M))
      hWmeas (fun p => c p.1 p.2)
      (fun p => (hc p.1 p.2).1) (fun p => (hc p.1 p.2).2.2.2)
  have hcov (g : G) (x y : D) (hx : x ∈ S) (hy : y ∈ S) :
      c x y = (W g x : Algebra M) * c (shift g x) (shift g y) * star (W g y : Algebra M) := by
    have hgen (t : G) :
        (W g x : Algebra M) *
          ((W t (shift g x) : Algebra M) * star (W t (shift g y) : Algebra M)) *
          star (W g y : Algebra M) =
        (W (g * t) x : Algebra M) * star (W (g * t) y : Algebra M) := by
      rw [hW g t x hx, hW g t y hy, star_mul]
      noncomm_ring
    apply diagonal_least_covariance J hJ (W g x) (W g y)
      (s := diagonalGenerators W (shift g x) (shift g y))
      (t := diagonalGenerators W x y) ?_ ?_
      (hc (shift g x) (shift g y)).1 (hc x y).1
      (hc (shift g x) (shift g y)).2.2.2 (hc x y).2.2.2
    · rintro _ ⟨t, rfl⟩
      exact ⟨g * t, (hgen t).symm⟩
    · rintro _ ⟨t, rfl⟩
      refine ⟨g⁻¹ * t, ?_⟩
      have heq := hgen (g⁻¹ * t)
      rw [mul_inv_cancel_left] at heq
      dsimp only
      rw [← heq]
      symm
      calc
        _ = (star (W g x : Algebra M) * (W g x : Algebra M)) *
            ((W (g⁻¹ * t) (shift g x) : Algebra M) *
              star (W (g⁻¹ * t) (shift g y) : Algebra M)) *
            (star (W g y : Algebra M) * (W g y : Algebra M)) := by noncomm_ring
        _ = _ := by
          rw [Unitary.star_mul_self_of_mem (W g x).property,
            Unitary.star_mul_self_of_mem (W g y).property, one_mul, mul_one]
  have hunit (x y : D) : IsUnit (c x y) := by
    nontriviality Algebra M
    exact (Units.ofNearby 1 (c x y) (by simpa using ((hc x y).2.2.1).trans_lt hr)).isUnit
  have hp (x y : D) := exists_polar_unitary_near_one (c x y) (((hc x y).2.2.1).trans_lt hr)
  choose a ha han using hp
  refine ⟨a, ?_, ?_, ?_⟩
  · exact aestronglyMeasurable_polar_trace τ J hJ
      (fun p : D × D => c p.1 p.2) (fun p : D × D => a p.1 p.2) hr
      (fun p => (hc p.1 p.2).2.2.1) (fun p => ha p.1 p.2) hcm
  · intro x y
    exact (han x y).trans (mul_le_mul_of_nonneg_left (hc x y).2.2.1 (by norm_num))
  · intro g x y hx hy
    exact polar_unitary_sandwich (hunit x y) (W g x) (W g y)
      (a x y) (a (shift g x) (shift g y)) (ha x y) (ha _ _) (hcov g x y hx hy)

end Local

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.KadisonKastler.exists_measurable_diagonal_unitary_on_set_oai.{u_1, u_2, u_3, u_4} := @OAI.KadisonKastler.exists_measurable_diagonal_unitary_on_set_oai.{u_1, u_2, u_3, u_4}
