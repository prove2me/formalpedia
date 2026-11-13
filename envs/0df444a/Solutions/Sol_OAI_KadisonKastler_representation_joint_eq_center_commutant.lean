-- Prove2me | solution 1 for OAI.KadisonKastler.representation_joint_eq_center_commutant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:44:08.420078+00:00
-- url     : https://prove2.me/submissions/7b74c28b-92ba-4b6e-8fcf-b504661e7139

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.List.Induction
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Option
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_OAIQ075A005
import Definitions.Def_OAIQ075A006
import Definitions.Def_Q260K002
import Theorems.Thm_OAI_KadisonKastler_representationVonNeumannAlgebra_eq_generated
import Theorems.Thm_OAI_KadisonSimilarity_subtype_star_range

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_JointCStarSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common separable source for an algebra and its commutant

Taking the norm closure of the joint star algebra preserves norm separability.
When the two sources generate `P` and `P'`, the common source generates the
commutant of the center. This puts both sources in one fiber representation.
-/

noncomputable section
namespace KadisonSimilarity

open scoped Topology

variable {A : Type*} [CStarAlgebra A]

theorem jointCStarSource_minimal (B C S : StarSubalgebra ℂ A)
    (hB : B ≤ S) (hC : C ≤ S) (hS : IsClosed (S : Set A)) :
    jointCStarSource B C ≤ S :=
  StarSubalgebra.topologicalClosure_minimal (sup_le hB hC) hS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem source_commutant_eq
    (B : StarSubalgebra ℂ (H →L[ℂ] H)) (P : VonNeumannAlgebra H)
    (hB : (starSubalgebraCommutant B).commutant = P) :
    starSubalgebraCommutant B = P.commutant := by
  have h := congrArg VonNeumannAlgebra.commutant hB
  simpa only [VonNeumannAlgebra.commutant_commutant] using h

/-- The joint source has exactly the original center as commutant. -/
theorem jointCStarSource_commutant
    (P : VonNeumannAlgebra H) (B C : StarSubalgebra ℂ (H →L[ℂ] H))
    (hB : B ≤ P.toStarSubalgebra) (hC : C ≤ P.commutant.toStarSubalgebra)
    (hBgen : (starSubalgebraCommutant B).commutant = P)
    (hCgen : (starSubalgebraCommutant C).commutant = P.commutant) :
    starSubalgebraCommutant (jointCStarSource B C) = vonNeumannCenter P := by
  have hB' := source_commutant_eq B P hBgen
  have hC' : starSubalgebraCommutant C = P := by
    simpa only [VonNeumannAlgebra.commutant_commutant] using
      source_commutant_eq C P.commutant hCgen
  have hclosed : IsClosed ((vonNeumannCenter P).commutant.toStarSubalgebra :
      Set (H →L[ℂ] H)) := by
    change IsClosed ((vonNeumannCenter P).commutant : Set (H →L[ℂ] H))
    rw [VonNeumannAlgebra.coe_commutant]
    exact Set.isClosed_centralizer _
  have hBcentral : B ≤ (vonNeumannCenter P).commutant.toStarSubalgebra :=
    hB.trans (le_center_commutant P)
  have hCcentral : C ≤ (vonNeumannCenter P).commutant.toStarSubalgebra := by
    intro x hx
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro z hz
    exact (VonNeumannAlgebra.mem_commutant_iff.mp (hC hx)) z hz.1
  have hS := jointCStarSource_minimal B C _ hBcentral hCcentral hclosed
  apply VonNeumannAlgebra.ext
  intro T
  constructor
  · intro hT
    have hcomm : ∀ x ∈ jointCStarSource B C, x * T = T * x := by
      simpa only [← SetLike.mem_coe, coe_starSubalgebraCommutant,
        Set.mem_centralizer_iff] using hT
    have hTB : T ∈ starSubalgebraCommutant B := by
      simpa only [← SetLike.mem_coe, coe_starSubalgebraCommutant,
        Set.mem_centralizer_iff] using
        (show ∀ x ∈ B, x * T = T * x from fun x hx =>
          hcomm x (le_jointCStarSource_left B C hx))
    have hTC : T ∈ starSubalgebraCommutant C := by
      simpa only [← SetLike.mem_coe, coe_starSubalgebraCommutant,
        Set.mem_centralizer_iff] using
        (show ∀ x ∈ C, x * T = T * x from fun x hx =>
          hcomm x (le_jointCStarSource_right B C hx))
    rw [hB'] at hTB
    rw [hC'] at hTC
    exact ⟨hTC, hTB⟩
  · intro hT
    rw [← SetLike.mem_coe, coe_starSubalgebraCommutant]
    intro x hx
    exact ((VonNeumannAlgebra.mem_commutant_iff.mp (hS hx)) T hT).symm

theorem jointCStarSource_bicommutant
    (P : VonNeumannAlgebra H) (B C : StarSubalgebra ℂ (H →L[ℂ] H))
    (hB : B ≤ P.toStarSubalgebra) (hC : C ≤ P.commutant.toStarSubalgebra)
    (hBgen : (starSubalgebraCommutant B).commutant = P)
    (hCgen : (starSubalgebraCommutant C).commutant = P.commutant) :
    (starSubalgebraCommutant (jointCStarSource B C)).commutant =
      (vonNeumannCenter P).commutant :=
  congrArg VonNeumannAlgebra.commutant (jointCStarSource_commutant P B C hB hC hBgen hCgen)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonCentralGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The joint source generates the central commutant -/

namespace KadisonKastler

open KadisonSimilarity

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem representation_joint_eq_center_commutant_oai (M : VonNeumannAlgebra H)
    (A C : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (A : Set (H →L[ℂ] H))] [IsClosed (C : Set (H →L[ℂ] H))]
    (hA : generatedVonNeumannAlgebra A = M)
    (hC : (starSubalgebraCommutant C).commutant = M.commutant)
    (hAM : A ≤ M.toStarSubalgebra) (hCM : C ≤ M.commutant.toStarSubalgebra) :
    representationVonNeumannAlgebra (jointCStarSource A C).subtype =
      (vonNeumannCenter M).commutant := by
  have hAg : (starSubalgebraCommutant A).commutant = M := by
    simpa only [representationVonNeumannAlgebra, subtype_star_range, hA] using
      (representationVonNeumannAlgebra_eq_generated A.subtype)
  change (starSubalgebraCommutant (jointCStarSource A C).subtype.range).commutant = _
  rw [subtype_star_range]
  exact jointCStarSource_bicommutant M A C hAM hCM hAg hC

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.representation_joint_eq_center_commutant_oai.{u_1} := @OAI.KadisonKastler.representation_joint_eq_center_commutant_oai.{u_1}
