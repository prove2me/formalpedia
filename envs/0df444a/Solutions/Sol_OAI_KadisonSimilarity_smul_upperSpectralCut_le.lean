-- Prove2me | solution 1 for OAI.KadisonSimilarity.smul_upperSpectralCut_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:52:53.255385+00:00
-- url     : https://prove2.me/submissions/089209e7-93eb-4390-9e86-14d55ae1a886

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Nat.Pairing
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Option
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_OAIQ075A012

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralStepDischarge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete spectral cut projections

We construct the spectral cuts from the closed range of the positive part.
The construction takes place in the represented Hilbert space; bicommutant
closure proves membership in the given von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem rangeSupport_isStarProjection (B : H →L[ℂ] H) :
    IsStarProjection (rangeSupport B) :=
  ⟨Submodule.isIdempotentElem_starProjection _, isSelfAdjoint_starProjection _⟩

theorem rangeSupport_mul (B : H →L[ℂ] H) : rangeSupport B * B = B := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr
    (Submodule.le_topologicalClosure _ ⟨x, rfl⟩)

theorem mul_rangeSupport (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) :
    B * rangeSupport B = B := by
  have h := congrArg star (rangeSupport_mul B)
  simpa only [star_mul, hB.star_eq, (rangeSupport_isStarProjection B).isSelfAdjoint.star_eq]
    using h

/-- Annihilating the range also annihilates its orthogonal support. -/
theorem mul_rangeSupport_eq_zero (B C : H →L[ℂ] H) (h : C * B = 0) :
    C * rangeSupport B = 0 := by
  have hh : operatorRangeClosure B ≤ C.ker := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      exact congrArg (fun S : H →L[ℂ] H => S x) h
    · exact C.isClosed_ker
  ext x
  exact hh ((operatorRangeClosure B).starProjection_apply_mem x)

theorem upperSpectralCut_isStarProjection (A : H →L[ℂ] H) (t : ℝ) :
    IsStarProjection (upperSpectralCut A t) := rangeSupport_isStarProjection _

/-- Multiplication by a cut removes the negative part of the shifted operator. -/
theorem shifted_mul_upperSpectralCut (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    (A - t • 1) * upperSpectralCut A t = (A - t • 1)⁺ := by
  let B := A - t • (1 : H →L[ℂ] H)
  have hB : IsSelfAdjoint B := by
    dsimp [B]
    exact hA.sub ((IsSelfAdjoint.all t).smul (IsSelfAdjoint.one (H →L[ℂ] H)))
  change B * rangeSupport B⁺ = B⁺
  nth_rw 1 [← CFC.posPart_sub_negPart B hB]
  rw [sub_mul]
  rw [mul_rangeSupport B⁺ (CFC.posPart_nonneg B).isSelfAdjoint,
    mul_rangeSupport_eq_zero B⁺ B⁻ (CFC.negPart_mul_posPart B), sub_zero]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralCutBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative high spectral cuts. The discarded part has small operator
norm, and positivity bounds the trace of the retained projection. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem upperSpectralCut_commutes_self (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    Commute (upperSpectralCut A t) A := by
  have h : Commute (A - t • 1) A := by
    change (A - t • 1) * A = A * (A - t • 1)
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hp : Commute (A - t • 1)⁺ A := by
    rw [CFC.posPart_def]
    exact h.cfcₙ_real _
  exact rangeSupport_commutes _ A hp (by simpa only [hA.star_eq] using hp)

/-- The high cut of a positive operator is bounded in order by that operator. -/
theorem smul_upperSpectralCut_le_oai (A : H →L[ℂ] H) (hA : 0 ≤ A) (t : ℝ) :
    t • upperSpectralCut A t ≤ A := by
  let p := upperSpectralCut A t
  have hp : IsStarProjection p := upperSpectralCut_isStarProjection A t
  have hpa : Commute p A := upperSpectralCut_commutes_self A hA.isSelfAdjoint t
  have hc : Commute A (1 - p) := by
    change A * (1 - p) = (1 - p) * A
    rw [mul_sub, sub_mul, mul_one, one_mul, hpa.eq]
  have hfirst : 0 ≤ A * (1 - p) := Commute.mul_nonneg hA hp.one_sub.nonneg hc
  have hsecond : 0 ≤ (A - t • 1) * p := by
    rw [shifted_mul_upperSpectralCut A hA.isSelfAdjoint t]
    exact CFC.posPart_nonneg _
  apply sub_nonneg.mp
  have heq : A - t • p = A * (1 - p) + (A - t • 1) * p := by
    simp only [mul_sub, sub_mul, mul_one, smul_mul_assoc, one_mul]
    abel
  rw [heq]
  exact add_nonneg hfirst hsecond

end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonSimilarity.smul_upperSpectralCut_le_oai.{u_1} := @OAI.KadisonSimilarity.smul_upperSpectralCut_le_oai.{u_1}
