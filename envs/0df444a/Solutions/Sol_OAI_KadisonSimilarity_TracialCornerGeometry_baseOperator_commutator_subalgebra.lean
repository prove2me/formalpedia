-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator_commutator_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:44:53.032553+00:00
-- url     : https://prove2.me/submissions/4e7467de-6805-4b5d-962f-fe16a6b178b5

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
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
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A016

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialBaseSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed base Hilbert space of a represented tracial star algebra,
its actual inclusion, and compression of the ambient left action. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

theorem baseInclusion_intertwines (a : A) :
    (G.left (a : P)).comp (G.baseInclusion A).toContinuousLinearMap =
      (G.baseInclusion A).toContinuousLinearMap.comp (G.baseRepresentation A a) := rfl

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_BaseCommutatorCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compression of commutators with base-algebra elements needs no invariance
hypothesis on the other operator. This also restores the original operator
after the free-product symmetrization. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- The adjoint base inclusion intertwines every base-algebra element. -/
theorem baseInclusion_adjoint_intertwines (a : A) :
    (G.baseInclusion A).toContinuousLinearMap.adjoint.comp (G.left (a : P)) =
      (G.baseRepresentation A a).comp (G.baseInclusion A).toContinuousLinearMap.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (G.baseInclusion_intertwines A (star a))
  have hleft : (G.left ((star a : A) : P)).adjoint = G.left (a : P) := by
    change (G.left (star (a : P))).adjoint = G.left (a : P)
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint]
  have hbase : (G.baseRepresentation A (star a)).adjoint = G.baseRepresentation A a := by
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint]
  simpa only [ContinuousLinearMap.adjoint_comp, hleft, hbase] using h


/-- Compression commutes with the commutator against a base element. -/
theorem baseOperator_commutator_subalgebra_oai (Y : H →L[ℂ] H) (a : A) :
    G.baseOperator A (commutator Y (G.left (a : P))) =
      commutator (G.baseOperator A Y) (G.baseRepresentation A a) := by
  unfold baseOperator commutator
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
  rw [G.baseInclusion_intertwines A a]
  simp only [← ContinuousLinearMap.comp_assoc]
  rw [G.baseInclusion_adjoint_intertwines A a]

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator_commutator_subalgebra_oai.{u_1, u_2} := @OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator_commutator_subalgebra_oai.{u_1, u_2}
