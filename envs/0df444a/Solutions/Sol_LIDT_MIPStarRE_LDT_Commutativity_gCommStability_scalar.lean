-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.gCommStability_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:50:29.629921+00:00
-- url     : https://prove2.me/submissions/81c2d7a5-6429-4d72-a54d-a91c2eaff613

-- Generated proof for MIPStarRE.LDT.Commutativity.gCommStability_scalar.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_scalar_pointwise_cauchy_schwarz_bound

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Basic/TensorPlacement.lean. -/
/-!
# Tensor-placement helper lemmas and sandwich tensor estimates

Tensor-sum commutation, positivity/boundedness preservation,
factoring lemmas, and sandwich-residual estimates used in
the main induction step and polynomial-agreement arguments.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Tensor-placement helper lemmas -/





































/-- The total left-register expectation of a submeasurement is at most one on
a normalized bipartite state. -/
theorem sum_ev_leftTensor_outcome_le_one {α : Type*} [Fintype α]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (hnorm : ψ.IsNormalized) (A : SubMeas α ι) :
    ∑ a : α, ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) ≤ 1 := by
  calc
    ∑ a : α, ev ψ (leftTensor (ι₂ := ι) (A.outcome a))
      = ev ψ (leftTensor (ι₂ := ι) A.total) := by
          exact (ev_leftTensor_total_eq_sum_outcome ψ A).symm
    _ ≤ ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact ev_mono ψ _ _ <| leftTensor_le_one (ι₂ := ι) A.total_le_one
    _ = 1 := ev_one_of_isNormalized ψ hnorm



namespace SubMeas



end SubMeas

/-! ### Sandwich tensor estimates -/





end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Commutativity/GCommStability/Scalar/Common.lean. -/
/-!
# Section 11 commutativity: shared scalar stability helpers

Auxiliary positivity, order, and bounded-residual lemmas used by the scalar stability estimates.
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace GCommStability.Scalar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]









lemma storedResidual_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (zeta : Error)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ∀ x : Fq params, 0 ≤ hbound.storedResidual G x := by
  intro x
  unfold IdxPolyFamily.SliceBoundednessInput.storedResidual
  apply ev_nonneg_of_psd
  rw [leftTensor_mul_rightTensor_eq_opTensor]
  simpa [opTensor] using
    MIPStarRE.Quantum.kronecker_nonneg
      (sub_nonneg.mpr (G x).total_le_one)
      (hbound.sliceOpPSD x)


end GCommStability.Scalar

end MIPStarRE.LDT.Commutativity

end

/- Source helpers from MIPStarRE/LDT/Test/StrategyPolynomialFamilies.lean. -/
/-!
# Polynomial-family interfaces for the low individual degree test

Packaged slice-indexed polynomial-family interfaces extracted from
`MIPStarRE.LDT.Test.Strategy`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Polynomial-family interfaces -/



-- NOTE: no global `Inhabited` instance for `IdxPolyFamily`; without an actual
-- slice family, any default would be a degenerate zero-family placeholder.

namespace IdxPolyFamily









































namespace SliceBoundednessInput



/-- Stored residual half of the boundedness hypothesis.

This is exactly the paper's `(I-G^x) ⊗ Z^x` residual bound from
`references/ldt-paper/commutativity-G.tex`. -/
theorem storedBoundedResidualBound {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SymStrat params.next ι}
    {family : IdxPolyFamily params ι} {zeta : Error}
    (hbound : SliceBoundednessInput strategy family zeta)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    avgOver (uniformDistribution (Fq params))
      (fun x => hbound.storedResidual G x) ≤ zeta := by
  simpa [storedResidual, hG] using hbound.sliceBoundedness



end SliceBoundednessInput

end IdxPolyFamily

end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Section 11 commutativity: first scalar stability bound

The first scalar stability defect and its Cauchy--Schwarz boundedness proof.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open GCommStability.Scalar
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hnorm : strategy.state.IsNormalized)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (G : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    |_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityScalarDefect params strategy family G)| ≤ Real.sqrt zeta := by
  have h𝒟 :
      ∑ y ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)).support,
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)).weight y ≤ 1 := by
    simpa using _root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Fq params)
  calc
    |_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityScalarDefect params strategy family G)|
      ≤ Real.sqrt
          (_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
            (fun y => hbound.storedResidual G y)) := by
          exact
            _root_.LIDT.MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityScalarDefect params strategy family G)
              (fun y => hbound.storedResidual G y)
              (fun y => by
                simpa [_root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityScalarDefect] using
                  _root_.LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar.scalar_pointwise_cauchy_schwarz_bound
                    params strategy zeta family G hG hbound
                    (_root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityR params family y) y
                    (_root_.LIDT.MIPStarRE.LDT.sum_ev_leftTensor_outcome_le_one strategy.state hnorm
                      (_root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityR params family y)))
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar.storedResidual_nonneg
                params strategy family G zeta hbound)
              h𝒟
    _ ≤ Real.sqrt zeta := by
          exact Real.sqrt_le_sqrt <|
            hbound.storedBoundedResidualBound G hG
