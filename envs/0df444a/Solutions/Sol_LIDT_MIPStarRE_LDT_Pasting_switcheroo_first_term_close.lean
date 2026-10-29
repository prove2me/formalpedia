-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.switcheroo_first_term_close
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:35:13.860744+00:00
-- url     : https://prove2.me/submissions/b8a37d3a-c49f-4f42-a027-3394d850e50e

-- Generated proof for MIPStarRE.LDT.Pasting.switcheroo_first_term_close.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_avgOver_abs_le_avgOver_abs
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooSelfConsistency_bip
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_switchSandwich_leftTransfer
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_switchSandwich_rightTransfer

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/Completeness.lean. -/
/-!
# Switch-sandwich main: completeness estimate

`prop:switch-sandwich` assembled from the left and right transfer steps on a
normalized quantum state with a subprobability distribution.

## References

- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- `prop:switch-sandwich`.

The paper proof assumes a normalized state and a probability distribution
(weights summing to ≤ 1). These are now explicit hypotheses `hψ` and `h𝒟`. -/
theorem switchSandwich {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) (hB : OpBounded01 B)
    (δ : Error) :
    BipartiteSDDRel ψ 𝒟
      (IdxProjSubMeas.toIdxSubMeas A)
      (IdxProjSubMeas.toIdxSubMeas A) δ →
    SwitchSandwichStmt ψ 𝒟 A B δ := by
  intro happrox
  exact {
    leftSandwichTransfer :=
      switchSandwich_leftTransfer ψ 𝒟 hψ h𝒟 A B hB δ happrox
    rightSandwichTransfer :=
      switchSandwich_rightTransfer ψ 𝒟 hψ h𝒟 A B hB δ happrox
  }





end MIPStarRE.LDT.Preliminaries

end

end LIDT

open LIDT
/-!
# Section 12 pasting: switcheroo centers

Switcheroo center terms and their sandwich rewrites.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    {Outcome : Type*} [Fintype Outcome]
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (M : _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) Outcome ι)
    (omega : _root_.LIDT.MIPStarRE.LDT.Error)
    (hselfM : _root_.LIDT.MIPStarRE.LDT.SDDRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooSelfConsistencyLeft params M)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooSelfConsistencyRight params M)
      omega) :
    let firstTerm :=
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
        (fun x => _root_.LIDT.MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
          M ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total))
    let commonTerm :=
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
        (fun x => _root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
          M ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total))
    |firstTerm - commonTerm| ≤ 2 * Real.sqrt omega := by
  dsimp
  let L : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.Error := fun x =>
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
      M ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total)
  let C : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.Error := fun x =>
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
      M ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total)
  have hselfM_bip := _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooSelfConsistency_bip params ψbi M omega hselfM
  have hpoint : ∀ x, |L x - C x| ≤ 2 * Real.sqrt omega := by
    intro x
    have hB : _root_.LIDT.MIPStarRE.LDT.Preliminaries.OpBounded01 ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total) := by
      refine ⟨?_, ?_⟩
      · exact _root_.LIDT.MIPStarRE.LDT.SubMeas.total_nonneg (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x)
      · exact sub_nonneg.mpr (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total_le_one
    simpa [L, C] using
      (_root_.LIDT.MIPStarRE.LDT.Preliminaries.switchSandwich ψbi
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
        hnorm
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
        M
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total)
        hB
        omega
        hselfM_bip).leftSandwichTransfer
  calc
    |_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params)) L -
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params)) C|
      = |_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params)) (fun x => L x - C x)| := by
          simp [_root_.LIDT.MIPStarRE.LDT.avgOver, Finset.sum_sub_distrib, mul_sub]
    _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params)) (fun x => |L x - C x|) := by
          exact _root_.LIDT.MIPStarRE.LDT.Pasting.avgOver_abs_le_avgOver_abs _ _
    _ ≤ 2 * Real.sqrt omega := by
          exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_le_const
            (fun x : _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params => |L x - C x|)
            (2 * Real.sqrt omega)
            hpoint
