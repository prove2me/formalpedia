-- Prove2me | solution 1 for OAI.KadisonKastler.preservesJordan_of_map_unitary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:55:45.904901+00:00
-- url     : https://prove2.me/submissions/84ee384a-db38-4276-808b-c6222adf76b6

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Sequences
import Definitions.Def_Q260K002
import Definitions.Def_Q260K005
import Theorems.Thm_OAI_KadisonKastler_map_star_square_of_map_unitary

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralJordanMap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Jordan structure of a unitary-preserving map on a von Neumann algebra

Projection phases give exact algebraic identities on finite spectral
sums. Norm approximation by those sums then gives adjoint and square
preservation; complex polarization gives the Jordan identity.
-/

namespace KadisonKastler

open scoped BigOperators ComplexStarModule

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

private theorem map_jordan_of_three_squares (F : A →ₗ[ℂ] B) (a b : A)
    (ha : F (a * a) = F a * F a) (hb : F (b * b) = F b * F b)
    (hab : F ((a + b) * (a + b)) = F (a + b) * F (a + b)) :
    F (a * b + b * a) = F a * F b + F b * F a := by
  have he : (F a * F a + F (a * b + b * a)) + F b * F b =
      (F a * F a + (F a * F b + F b * F a)) + F b * F b := by
    calc
      _ = F ((a + b) * (a + b)) := by
        rw [show (a + b) * (a + b) = a * a + (a * b + b * a) + b * b by noncomm_ring]
        simp only [map_add, ha, hb]
      _ = F (a + b) * F (a + b) := hab
      _ = _ := by rw [map_add]; noncomm_ring
  exact add_left_cancel (add_right_cancel he)

/-- The same map is a star-preserving Jordan map, ready for the
surjective orientation theorem. -/
theorem preservesJordan_of_map_unitary_oai
    (F : Algebra M →L[ℂ] B) (hF1 : F 1 = 1)
    (hFu : ∀ u : unitary (Algebra M), F u ∈ unitary B) :
    PreservesJordan F.toLinearMap := by
  intro x y
  exact map_jordan_of_three_squares F.toLinearMap x y
    (map_star_square_of_map_unitary F hF1 hFu x).2
    (map_star_square_of_map_unitary F hF1 hFu y).2
    (map_star_square_of_map_unitary F hF1 hFu (x + y)).2

end

end KadisonKastler

end OAI
end

theorem solution.{u_2, u_3} : type_of% @OAI.KadisonKastler.preservesJordan_of_map_unitary_oai.{u_2, u_3} := @OAI.KadisonKastler.preservesJordan_of_map_unitary_oai.{u_2, u_3}
