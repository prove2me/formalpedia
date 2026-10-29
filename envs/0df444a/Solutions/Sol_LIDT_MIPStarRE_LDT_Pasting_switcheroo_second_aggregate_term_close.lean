-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.switcheroo_second_aggregate_term_close
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:35:13.484311+00:00
-- url     : https://prove2.me/submissions/b4af9561-7b39-4b9d-a232-3446db26120d

-- Generated proof for MIPStarRE.LDT.Pasting.switcheroo_second_aggregate_term_close.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_avgOver_abs_le_avgOver_abs
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_completePartProjFamily_selfConsistency_generic
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
# Section 12 pasting: switcheroo second term

Complete-part self-consistency and the second switcheroo term.
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
    (zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hselfG : _root_.LIDT.MIPStarRE.LDT.Pasting.GCompleteSelfConsistencyStatement params ψbi family zeta) :
    let secondTerm := _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateSecondTerm params ψbi family M
    let commonTerm :=
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
        (fun y => _root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily params family) (((M y).toSubMeas).total))
    |secondTerm - commonTerm| ≤ 2 * Real.sqrt zeta := by
  let 𝒟x : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params) := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params)
  let Gcomplete : _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params) Unit ι :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily params family
  let L : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.Error := fun y =>
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi 𝒟x Gcomplete (((M y).toSubMeas).total)
  let C : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.Error := fun y =>
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi 𝒟x Gcomplete (((M y).toSubMeas).total)
  change |_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateSecondTerm params ψbi family M - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟x C| ≤
    2 * Real.sqrt zeta
  have hselfG_complete :
      _root_.LIDT.MIPStarRE.LDT.SDDRel ψbi 𝒟x
        (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooSelfConsistencyLeft params Gcomplete)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooSelfConsistencyRight params Gcomplete)
        zeta := by
    simpa [𝒟x, Gcomplete] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily_selfConsistency_generic params ψbi family zeta hselfG
  have hselfG_bip := _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooSelfConsistency_bip params ψbi Gcomplete zeta hselfG_complete
  have hpoint : ∀ y, |L y - C y| ≤ 2 * Real.sqrt zeta := by
    intro y
    have hB : _root_.LIDT.MIPStarRE.LDT.Preliminaries.OpBounded01 (((M y).toSubMeas).total) := by
      refine ⟨?_, ?_⟩
      · exact _root_.LIDT.MIPStarRE.LDT.SubMeas.total_nonneg ((M y).toSubMeas)
      · exact sub_nonneg.mpr ((M y).toSubMeas).total_le_one
    simpa [L, C, 𝒟x, Gcomplete] using
      (_root_.LIDT.MIPStarRE.LDT.Preliminaries.switchSandwich ψbi
        𝒟x
        hnorm
        (by simpa [𝒟x] using _root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
        Gcomplete
        (((M y).toSubMeas).total)
        hB
        zeta
        hselfG_bip).leftSandwichTransfer
  have hsecond_eq :
      _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateSecondTerm params ψbi family M =
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟x L := by
    change
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
          (fun q =>
            ∑ o : Outcome,
              _root_.LIDT.MIPStarRE.LDT.ev ψbi
                (_root_.LIDT.MIPStarRE.LDT.leftTensor
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total * (M q.2).outcome o *
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total))) =
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟x L
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
          (fun q =>
            ∑ o : Outcome,
              _root_.LIDT.MIPStarRE.LDT.ev ψbi
                (_root_.LIDT.MIPStarRE.LDT.leftTensor
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total * (M q.2).outcome o *
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total)))
        = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
            (fun y =>
              _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
                (fun x =>
                  ∑ o : Outcome,
                    _root_.LIDT.MIPStarRE.LDT.ev ψbi
                      (_root_.LIDT.MIPStarRE.LDT.leftTensor
                        ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total * (M y).outcome o *
                          (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total)))) := by
              calc
                _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
                    (fun q =>
                      ∑ o : Outcome,
                        _root_.LIDT.MIPStarRE.LDT.ev ψbi
                          (_root_.LIDT.MIPStarRE.LDT.leftTensor
                            ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                              (M q.2).outcome o *
                              (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total))) =
                  _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
                    (fun q =>
                      ∑ o : Outcome,
                        _root_.LIDT.MIPStarRE.LDT.ev ψbi
                          (_root_.LIDT.MIPStarRE.LDT.leftTensor
                            ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.2).total *
                              (M q.1).outcome o *
                              (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.2).total))) := by
                        simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion] using
                          (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv
                            (α := _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)
                            (β := _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)
                            (Equiv.prodComm (_root_.LIDT.MIPStarRE.LDT.Fq params) (_root_.LIDT.MIPStarRE.LDT.Fq params))
                            (fun q =>
                              ∑ o : Outcome,
                                _root_.LIDT.MIPStarRE.LDT.ev ψbi
                                  (_root_.LIDT.MIPStarRE.LDT.leftTensor
                                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                                      (M q.2).outcome o *
                                      (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total))))
                _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
                      (fun y =>
                        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
                          (fun x =>
                            ∑ o : Outcome,
                              _root_.LIDT.MIPStarRE.LDT.ev ψbi
                                (_root_.LIDT.MIPStarRE.LDT.leftTensor
                                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total *
                                    (M y).outcome o *
                                    (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total)))) := by
                        simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion, _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion] using
                          (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod
                            (α := _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params)
                            (β := _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params)
                            (f := fun y x =>
                              ∑ o : Outcome,
                                _root_.LIDT.MIPStarRE.LDT.ev ψbi
                                  (_root_.LIDT.MIPStarRE.LDT.leftTensor
                                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total *
                                      (M y).outcome o *
                                      (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total))))
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟x L := by
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            intro y
            unfold L _root_.LIDT.MIPStarRE.LDT.Preliminaries.leftSandwichExpectation
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            intro x
            let G : _root_.LIDT.MIPStarRE.Quantum.Op ι := (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total
            have hGout : (Gcomplete x).outcome () = G := by
              simpa [Gcomplete, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily, G, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas,
                _root_.LIDT.MIPStarRE.LDT.postprocess] using (family.meas x).sum_eq_total
            calc
              ∑ o : Outcome,
                  _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (G * (M y).outcome o * G))
                = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (G * ((M y).toSubMeas).total * G)) := by
                    rw [← _root_.LIDT.MIPStarRE.LDT.ev_sum ψbi (fun o : Outcome =>
                      _root_.LIDT.MIPStarRE.LDT.leftTensor (G * (M y).outcome o * G))]
                    rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum]
                    congr 1
                    rw [← Finset.sum_mul, ← Finset.mul_sum, (M y).sum_eq_total]
              _ = ∑ _u : Unit,
                    _root_.LIDT.MIPStarRE.LDT.ev ψbi
                      (_root_.LIDT.MIPStarRE.LDT.leftTensor ((Gcomplete x).outcome ()) *
                        _root_.LIDT.MIPStarRE.LDT.leftTensor (((M y).toSubMeas).total) *
                        _root_.LIDT.MIPStarRE.LDT.leftTensor ((Gcomplete x).outcome ())) := by
                    simp [hGout, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor, mul_assoc]
  calc
    |_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateSecondTerm params ψbi family M - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟x C|
      = |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟x L - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟x C| := by rw [hsecond_eq]
    _ = |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟x (fun y => L y - C y)| := by
          simp [_root_.LIDT.MIPStarRE.LDT.avgOver, Finset.sum_sub_distrib, mul_sub]
    _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟x (fun y => |L y - C y|) := by
          exact _root_.LIDT.MIPStarRE.LDT.Pasting.avgOver_abs_le_avgOver_abs _ _
    _ ≤ 2 * Real.sqrt zeta := by
          simpa [𝒟x] using
            _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_le_const
              (fun y : _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params => |L y - C y|)
              (2 * Real.sqrt zeta)
              hpoint
