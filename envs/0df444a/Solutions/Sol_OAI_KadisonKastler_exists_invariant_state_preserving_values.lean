-- Prove2me | solution 1 for OAI.KadisonKastler.exists_invariant_state_preserving_values
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:01:02.164203+00:00
-- url     : https://prove2.me/submissions/56772e15-8d50-42a8-b422-8a0d80c02479

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Matrix.Composition
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K018

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugationAveragedState
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Invariant states obtained by the constructed scalar mean

The scalar orbit of the state is averaged, so every invariant restriction
is preserved even when the state is not normal. Strong invariance under
probability-measure averages is a separate step.
-/

namespace KadisonKastler

open NaimarkZFC
open scoped ComplexOrder BoundedContinuousFunction

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ScalarInvariantMean

variable (m : ScalarInvariantMean G) (U : G →* unitary (H →L[ℂ] H))

theorem averagedState_eq_of_invariant_values (φ : (H →L[ℂ] H) →L[ℂ] ℂ)
    (T : H →L[ℂ] H) (hT : ∀ g, φ (unitaryConj (U g) T)=φ T) :
    m.averagedState U φ T=φ T := by
  have he : stateOrbitScalar U φ T=BoundedContinuousFunction.const G (φ T) := by
    ext g
    exact hT g
  rw [averagedState_apply,he,m.fixed]

theorem averagedState_isState (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ) :
    IsState (m.averagedState U φ) := by
  apply (isState_iff _).mpr
  refine ⟨?_,fun T => ?_⟩
  · rw [m.averagedState_eq_of_invariant_values U φ 1 (fun g => by
      rw [show unitaryConj (U g) (1 : H →L[ℂ] H)=1 from
        (Unitary.conjStarAlgAut ℂ _ (U g)).map_one])]
    exact ((isState_iff φ).mp hφ).1
  · apply m.positive
    intro g
    change (φ ((Unitary.conjStarAlgAut ℂ _ (U g)) (star T*T))).im = 0 ∧
      0 ≤ (φ ((Unitary.conjStarAlgAut ℂ _ (U g)) (star T*T))).re
    let e : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H) :=
      Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U g)
    have he : e (star T*T)=star (e T)*e T := by
      calc
        _ = e (star T)*e T := e.map_mul _ _
        _ = _ := congrArg (fun a : H →L[ℂ] H => a*e T) (map_star e T)
    change (φ (e (star T*T))).im=0 ∧ 0 ≤ (φ (e (star T*T))).re
    rw [he]
    exact hφ.2 (e T)

theorem averagedState_invariant (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (g : G)
    (T : H →L[ℂ] H) :
    m.averagedState U φ (unitaryConj (U g) T) = m.averagedState U φ T := by
  have he : stateOrbitScalar U φ (unitaryConj (U g) T) =
      scalarMeanTranslate g⁻¹ (stateOrbitScalar U φ T) := by
    ext h
    change φ (unitaryConj (U h) (unitaryConj (U g) T))=φ (unitaryConj (U ((g⁻¹)⁻¹*h)) T)
    rw [← unitaryConj_mul,← map_mul,inv_inv,mul_comm h g]
  rw [averagedState_apply,he,m.invariant,← averagedState_apply]

end ScalarInvariantMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InvariantStateExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Invariant extensions preserving prescribed state values

The abelian action is averaged as a discrete group. No continuity or
normality of the initial ambient state is needed.
-/

namespace KadisonKastler

open NaimarkZFC

noncomputable section

variable {G H : Type*} [CommGroup G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_invariant_state_preserving_values_oai
    (U : G →* unitary (H →L[ℂ] H))
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ)
    (A : Set (H →L[ℂ] H))
    (hA : ∀ T ∈ A, ∀ g : G, φ (unitaryConj (U g) T)=φ T) :
    ∃ ψ : (H →L[ℂ] H) →L[ℂ] ℂ, IsState ψ ∧
      (∀ (g : G) (T : H →L[ℂ] H), ψ (unitaryConj (U g) T)=ψ T) ∧
      ∀ T ∈ A, ψ T=φ T := by
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  let m := abelianScalarInvariantMean G
  exact ⟨m.averagedState U φ,m.averagedState_isState U φ hφ,
    m.averagedState_invariant U φ,
    fun T hT => m.averagedState_eq_of_invariant_values U φ T (hA T hT)⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.exists_invariant_state_preserving_values_oai.{u_1, u_2} := @OAI.KadisonKastler.exists_invariant_state_preserving_values_oai.{u_1, u_2}
