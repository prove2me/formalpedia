-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeftFrontScalar_close_firstSplitScalar
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:06:53.379599+00:00
-- url     : https://prove2.me/submissions/9510659b-44c5-49fc-8b8d-9d02ecfb4158

-- Generated proof for MIPStarRE.LDT.Pasting.switcherooAggregateLeftFrontScalar_close_firstSplitScalar.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooAggregateLeftFront_contraction
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooPointProductLeft_self_eq_firstSplit_point
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooPointProductRightLeft_eq_leftFront_point

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Pasting/SwitcherooSetup/Infrastructure.lean. -/
/-!
# Section 12 pasting: switcheroo infrastructure

Initial switcheroo infrastructure and aggregate expansion helpers.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Switcheroo infrastructure -/





/-- Read the switcheroo point-product commutation hypothesis as an average
`qSDDCore` bound. -/
lemma switcherooPointProductCommutation_coreBound
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (chi : Error)
    (hcomm : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft params family M)
      (switcherooPointProductRight params family M)
      chi) :
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q => qSDDCore ψbi
          (fun go => (switcherooPointProductLeft params family M q).outcome go)
          (fun go => (switcherooPointProductRight params family M q).outcome go)) ≤
      chi := by
  simpa [sddErrorOp, qSDDOp] using hcomm.squaredDistanceBound









end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: fourth-term chain helpers

Internal helpers by convention for the fourth-term chain in `commutativitySwitcheroo`.
These were extracted from `SwitcherooCompletion` to keep that file under
the 1000-line threshold.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]









-- The last `χ`-step needs only pointwise normalization for the `G_g M_o`
-- factors inside `closenessOfInnerProduct_right`; the heavy adjoint rewrites are
-- isolated in the two pointwise helper lemmas above.

theorem solution
    {Outcome : Type*} [Fintype Outcome]
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (M : _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) Outcome ι)
    (chi : _root_.LIDT.MIPStarRE.LDT.Error)
    (hcomm : _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductLeft params family M)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductRight params family M)
      chi) :
    |_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeftFrontScalar params ψbi family M -
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstSplitScalar params ψbi family M| ≤
      Real.sqrt chi := by
  let 𝒟q : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params) :=
    _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)
  let A : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params → _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome →
      _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q go => ((_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductLeft params family M q).outcome go)ᴴ
  let B : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params → _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome →
      _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q go => ((_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductRight params family M q).outcome go)ᴴ
  let C : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params → _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome → Unit →
      _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q go () => (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductLeft params family M q).outcome go
  have h𝒟q : ∑ q ∈ 𝒟q.support, 𝒟q.weight q ≤ 1 := by
    simpa [𝒟q] using _root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)
  have hAB :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q
        (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi (fun go => (A q go)ᴴ) (fun go => (B q go)ᴴ)) ≤ chi := by
    simpa [𝒟q, A, B] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductCommutation_coreBound params ψbi family M chi hcomm
  have hC :
      ∀ q,
        (∑ go : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
            (∑ u : Unit, C q go u)ᴴ * (∑ u : Unit, C q go u)) ≤ 1 := by
    intro q
    simpa [C, _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductLeft, _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.orderedProductOpFamily,
        _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeftFront_contraction params family M q
  have hleft :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q (fun q =>
          ∑ a : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
            ∑ b : Unit, _root_.LIDT.MIPStarRE.LDT.ev ψbi (A q a * C q a b)) =
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstSplitScalar params ψbi family M := by
    unfold _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstSplitScalar
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro q
    refine Finset.sum_congr rfl ?_
    intro go _
    calc
      ∑ b : Unit, _root_.LIDT.MIPStarRE.LDT.ev ψbi (A q go * C q go b)
        = _root_.LIDT.MIPStarRE.LDT.ev ψbi (A q go * C q go ()) := by simp
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((M q.2).outcome go.2 *
                (family.meas q.1).outcome go.1 *
                (M q.2).outcome go.2)) := by
            simpa [A, C] using
              _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductLeft_self_eq_firstSplit_point
                (params := params) (ψbi := ψbi) (family := family) (M := M) q go
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((M q.2).outcome go.2 *
                ((family.meas q.1).outcome go.1 * (M q.2).outcome go.2))) := by
            simp [mul_assoc]
  have hright :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q (fun q =>
          ∑ a : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
            ∑ b : Unit, _root_.LIDT.MIPStarRE.LDT.ev ψbi (B q a * C q a b)) =
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeftFrontScalar params ψbi family M := by
    unfold _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeftFrontScalar
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro q
    refine Finset.sum_congr rfl ?_
    intro go _
    calc
      ∑ b : Unit, _root_.LIDT.MIPStarRE.LDT.ev ψbi (B q go * C q go b)
        = _root_.LIDT.MIPStarRE.LDT.ev ψbi (B q go * C q go ()) := by simp
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              (((family.meas q.1).outcome go.1) *
                (M q.2).outcome go.2 *
                (family.meas q.1).outcome go.1 *
                (M q.2).outcome go.2)) := by
            simpa [B, C] using
              _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductRightLeft_eq_leftFront_point
                (params := params) (ψbi := ψbi) (family := family) (M := M) q go
  have hleft' :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q (fun q =>
          ∑ a : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψbi (A q a * C q a ())) =
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstSplitScalar params ψbi family M := by
    simpa using hleft
  have hright' :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q (fun q =>
          ∑ a : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψbi (B q a * C q a ())) =
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeftFrontScalar params ψbi family M := by
    simpa using hright
  have hclose :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.closenessOfInnerProduct_right ψbi hnorm 𝒟q h𝒟q A B C chi hAB hC
  have hclose' :
      |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q (fun q =>
          ∑ a : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψbi (A q a * C q a ())) -
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q (fun q =>
          ∑ a : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψbi (B q a * C q a ()))| ≤
        Real.sqrt chi := by
    simpa using hclose
  simpa [hleft', hright', abs_sub_comm] using hclose'
