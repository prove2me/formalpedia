-- Prove2me | solution 1 for OAI.Generator.isII1Factor_of_starAlgEquiv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:40:57.850381+00:00
-- url     : https://prove2.me/submissions/de38a05e-544a-4f60-997b-5ae71bf3a29e

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_OAIQ075A009

section
-- module Solutions.OAIQ075_KS.FactorGeneration_TraceTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Literal weak-operator generation under a concrete star-algebra isomorphism.
Continuity is explicitly for the restricted WOT, not the operator norm topology.
This transport does not construct a trace representation of a finite factor. -/
section
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {S : StarSubalgebra ℂ (H →L[ℂ] H)}
  {T : StarSubalgebra ℂ (K →L[ℂ] K)}

/-! Transport of the unchanged finite diffuse factor predicate.
The algebraic fields use the actual star isomorphism; target WOT closedness
is explicit. No trace or separability conclusion is inferred. -/

theorem isII1Factor_of_starAlgEquiv_oai (e : S ≃⋆ₐ[ℂ] T)
    (hS : IsII1Factor S) (hT : WOTClosed T) : IsII1Factor T where
  nonzero := by
    intro h
    have ht : (0 : T) = 1 := Subtype.ext h
    have hs : (0 : S) = 1 := e.injective (by simpa only [map_zero, map_one] using ht)
    exact hS.nonzero (congrArg Subtype.val hs)
  weaklyClosed := hT
  factor := by
    intro x hx
    have hc : ∀ y : S, y * e.symm x = e.symm x * y := by
      intro y
      apply e.injective
      change e (y * e.symm x) = e (e.symm x * y)
      simpa only [map_mul, e.apply_symm_apply] using hx (e y)
    obtain ⟨c, hc⟩ := hS.factor (e.symm x) hc
    refine ⟨c, ?_⟩
    calc x = e (e.symm x) := (e.apply_symm_apply x).symm
         _ = e (algebraMap ℂ S c) := congrArg e hc
         _ = algebraMap ℂ T c := e.toAlgEquiv.commutes c
  finite := by
    intro v hv
    have h : star (e.symm v) * e.symm v = 1 := by
      simpa only [map_mul, map_star, map_one] using congrArg e.symm hv
    have hf := hS.finite (e.symm v) h
    simpa only [map_mul, map_star, map_one, e.apply_symm_apply] using congrArg e hf
  diffuse := by
    intro p hp hp0
    have hsp : IsStarProjection (e.symm p) := hp.map e.symm
    have hsp0 : e.symm p ≠ 0 := by
      intro hz
      apply hp0
      simpa only [e.apply_symm_apply, map_zero] using congrArg e hz
    obtain ⟨q, hq, hq0, hqp, hpq, hqp'⟩ := hS.diffuse (e.symm p) hsp hsp0
    refine ⟨e q, hq.map e, ?_, ?_, ?_, ?_⟩
    · intro hz
      apply hq0
      apply e.injective
      change e q = e 0
      simpa only [map_zero] using hz
    · intro heq
      apply hqp
      apply e.injective
      change e q = e (e.symm p)
      simpa only [e.apply_symm_apply] using heq
    · simpa only [map_mul, e.apply_symm_apply] using congrArg e hpq
    · simpa only [map_mul, e.apply_symm_apply] using congrArg e hqp'

end

/-! Compact original image balls and spectral clipping identify the actual
bicommutant with the original algebra's represented image. -/
open Filter
open scoped ComplexConjugate ComplexStarModule CStarAlgebra Pointwise Topology

/-! First step of generation transport: compact balls and closed vector balls
for the represented intersection with any original WOT-closed subalgebra. -/
open Filter
open scoped Topology CStarAlgebra

/-! Closed images of original WOT-closed subalgebras in the constructed representation. -/
open Filter
open scoped Topology CStarAlgebra ComplexStarModule

end Generator

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Generator.isII1Factor_of_starAlgEquiv_oai.{u_1, u_2} := @OAI.Generator.isII1Factor_of_starAlgEquiv_oai.{u_1, u_2}
