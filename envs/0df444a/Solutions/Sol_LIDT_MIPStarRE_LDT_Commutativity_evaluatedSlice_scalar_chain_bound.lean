-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_scalar_chain_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:22:26.048068+00:00
-- url     : https://prove2.me/submissions/90b8c01c-64fc-4aa8-8838-07abb9de1b1b

-- Generated proof for MIPStarRE.LDT.Commutativity.evaluatedSlice_scalar_chain_bound.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedSliceCommutation_avg_swap_terms
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseEight_tail_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseFivePaper_avg_diff_eq_neg_orderedDefect
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseFivePaper_reindex_to_raw_defect
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseFour_pointSwap_right_bound_of_commutativityPoints
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseNine_tail_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseOne_insert_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseSixSeven_reverse_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseTwo_questionDefect_avg_eq_stabilityDefect
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_gCommStabilityTwo_raw_scalar
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_gCommStability_scalar
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_leftRightTensor_prefix_pointMeasurement_normalization
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_leftTensor_prefix_total_normalization
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_consSubMeas

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Commutativity/EvaluatedSliceCommutation/Consequences.lean. -/
/-!
# Section 11 commutativity: evaluated-slice commutation consequences

Downstream consequences of the evaluated-slice commutation estimate: pulling
single-point evaluated-family self-consistency bounds up to evaluated-slice
questions.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Pull a single-point evaluated-family self-consistency bound up to the first
coordinate of an evaluated-slice question. -/
lemma evaluatedPointSelfConsistency_fst
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hssc : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta) :
    SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.1)
      (fun q => evaluatedPointFamilyRight params family q.1)
      zeta := by
  rcases hssc with ⟨h⟩
  constructor
  simpa [sddError] using
    (avgOver_uniform_fst (α := Point params.next) (β := Point params.next)
      (f := fun u =>
        qSDD strategy.state
          (evaluatedPointFamilyLeft params family u)
          (evaluatedPointFamilyRight params family u))).trans_le h

/-- Pull a single-point evaluated-family self-consistency bound up to the second
coordinate of an evaluated-slice question. -/
lemma evaluatedPointSelfConsistency_snd
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hssc : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta) :
    SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.2)
      (fun q => evaluatedPointFamilyRight params family q.2)
      zeta := by
  rcases hssc with ⟨h⟩
  constructor
  simpa [sddError] using
    (avgOver_uniform_snd (α := Point params.next) (β := Point params.next)
      (f := fun u =>
        qSDD strategy.state
          (evaluatedPointFamilyLeft params family u)
          (evaluatedPointFamilyRight params family u))).trans_le h

end MIPStarRE.LDT.Commutativity

end

/- Source helpers from MIPStarRE/LDT/Commutativity/Scaffold/Symmetry.lean. -/
/-!
# Section 11 commutativity: symmetry transport

Symmetry transport between coded `F_q` points and the underlying scalar model.
The lemmas below put the point-consistency relation into the orientations used
by the Section 11 commutativity argument.

## References

- `references/ldt-paper/commutativity-points.tex`
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The point-consistency relation written in local evaluated-point-family
notation. -/
lemma evaluatedPointFamily_pointConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (evaluatedPointFamily params family)
      zeta := by
  simpa [evaluatedPointFamily] using hcons.pointConsistency

/-- The evaluated-point consistency relation with the two families swapped.
This is the orientation needed by `Preliminaries.consSubMeas`, whose
submeasurement input comes first. -/
lemma evaluatedPointFamily_pointConsistency_swapped
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamily params family)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      zeta := by
  exact
    consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (evaluatedPointFamily params family)
      zeta
      (evaluatedPointFamily_pointConsistency params strategy family zeta hcons)

end MIPStarRE.LDT.Commutativity

end

/- Source helpers from MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG/MainChain.lean. -/
/-!
# Main scalar chain assembly

The core lemma `evaluatedSlice_scalar_chain_bound` that assembles the ten-step
scalar approximation chain for `lem:comm-data-processed-g`.  This is the
heavyweight proof corresponding to `references/ldt-paper/commutativity-G.tex`,
lines 72–131.  Phases 1, 3, 4, 6–7, and 8–9 are supplied by the reverse and
tail parts of the paper chain; Phase 2 uses the reindexing infrastructure from
`PhaseTwo`.
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]







/-- Normalization for the shared ProcessedG right-register point-swap prefix. -/
private lemma evaluatedSlice_pointSwap_right_prefix_normalization
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (T : EvaluatedSliceQuestion params → MIPStarRE.Quantum.Op ι)
    (hT_nonneg : ∀ q, 0 ≤ T q)
    (hT_le_one : ∀ q, T q ≤ 1) :
    ∀ q,
      ∑ ab : EvaluatedSliceOutcome params,
        evaluatedSlicePointSwapRightPrefix (ι := ι) params family T q ab *
            (evaluatedSlicePointSwapRightPrefix (ι := ι) params family T q ab)ᴴ ≤
          1 := by
  intro q
  simpa [evaluatedSlicePointSwapRightPrefix] using
    (leftTensor_prefix_total_normalization
      (A := evaluatedSliceFirstFactor params family q)
      (B := evaluatedSliceSecondFactor params family q)
      (T := T q)
      (hT_nonneg := hT_nonneg q)
      (hT_le_one := hT_le_one q))

private lemma evaluatedSlice_pointSwap_right_bound_of_norms
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (gamma : Error)
    (hnorm : strategy.state.IsNormalized)
    (hcomm :
      SDDOpRel strategy.state
        (uniformDistribution (PointPairQuestion params.next))
        (pointMeasurementProductLeft params.next strategy)
        (pointMeasurementProductRight params.next strategy)
        (commutativityPointsError params.next gamma))
    (C : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params →
      MIPStarRE.Quantum.Op (ι × ι))
    (hC : ∀ q, ∑ ab : EvaluatedSliceOutcome params, C q ab * (C q ab)ᴴ ≤ 1)
    (lhs rhs : EvaluatedSliceQuestion params → Error)
    (hlhs : avgOver (uniformDistribution (EvaluatedSliceQuestion params)) lhs =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSlicePhaseFourInserted (ι := ι) params strategy C))
    (hrhs : avgOver (uniformDistribution (EvaluatedSliceQuestion params)) rhs =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSlicePhaseFourSwapped (ι := ι) params strategy C)) :
    |avgOver (uniformDistribution (EvaluatedSliceQuestion params)) lhs -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params)) rhs| ≤
      6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
  have hswap :=
    evaluatedSlice_phaseFour_pointSwap_right_bound_of_commutativityPoints
      params strategy gamma hnorm hcomm C hC
  calc
    |avgOver (uniformDistribution (EvaluatedSliceQuestion params)) lhs -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params)) rhs|
      = |avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (evaluatedSlicePhaseFourInserted (ι := ι) params strategy C) -
          avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (evaluatedSlicePhaseFourSwapped (ι := ι) params strategy C)| := by
            rw [hlhs, hrhs]
    _ ≤ 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
          change
            |(avgOver (uniformDistribution (EvaluatedSliceQuestion params)) fun q =>
                  ∑ ab,
                    ev strategy.state
                      (C q ab *
                        rightTensor (ι₁ := ι)
                          ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2 *
                            (evaluatedSlicePointMeas params strategy q.1).outcome ab.1))) -
                avgOver (uniformDistribution (EvaluatedSliceQuestion params)) fun q =>
                  ∑ ab,
                    ev strategy.state
                      (C q ab *
                        rightTensor (ι₁ := ι)
                          ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1 *
                            (evaluatedSlicePointMeas params strategy q.2).outcome ab.2))| ≤
              6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error))
          exact hswap

/- Scalar approximation chain for the evaluated-slice commutation.

This is the core of the paper's proof of `lem:comm-data-processed-g`
(`references/ldt-paper/commutativity-G.tex`, lines 72–131).
Starting from `E[∑ ABAB]`, the proof applies ten approximation steps:

1. `≈_{2√ζ}`: insert Bob's measurement via `closenessOfIP` + `eq:add-an-a`
2. `≈_{√ζ}`: remove trailing `G^y` (`clm:g-comm-stability`)
3. `≈_{2√ζ}`: insert Bob's second measurement via `closenessOfIP` +
   `eq:add-an-a`
4. `≈_{6√(γ(m+1))}`: swap Bob's measurements via `closenessOfIP` +
   `commutativityPoints`
5a. `≈_{6√(γ(m+1))}`: the point-measurement swap contribution internal
    to the paper's `clm:g-comm-stability2` accounting
5b. `≈_{√ζ}`: remove trailing `G^x` by the boundedness part of
    `gCommStabilityTwo_raw_scalar` (this is the scalar part of `hphase5paper` below)
6–7. `≈_{2√ζ + 2√ζ}`: reverse the `eq:add-an-a` insertions
8–9. `≈_{√ζ + √ζ}`: apply postprocessed self-consistency twice

Summing: `Σεᵢ = 12√ζ + 12√(γ(m+1))`, so `2 * Σεᵢ ≤ 48m(√γ + √ζ)`. -/


end MIPStarRE.LDT.Commutativity

end

/- Source helpers from MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG/PhaseTwo.lean. -/
/-!
# Phase 2 stability defect infrastructure

Internal helper definitions and lemmas for the Phase 2 scalar bridge in
`ProcessedG`.  These definitions extract and bound the one-dimensional stability
defect controlled by `gCommStability_scalar` (the paper's `clm:g-comm-stability`),
reindex the question-level defect into the stability defect via finite
marginalization, and perform the subtraction algebra that rewrites the phase-2
insertion/removal difference as the negative defect.
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



/-- Direct `√ζ` control of the phase-2 stability defect.

The remaining bridge from the explicit evaluated-slice difference to this
one-dimensional defect is pure finite reindexing and averaging: expand
`totalSandwichFamily`, decompose the sampled second point as `(v,y)`, collect the
postprocessing fiber `∑_b ∑_{g : g(v)=b}` into `∑_g`, and average the first
sampled point into `gCommStabilityR`. -/
lemma evaluatedSlice_phaseTwo_stability_defect_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    |avgOver (uniformDistribution (Fq params))
      (evaluatedSlicePhaseTwoStabilityDefect params strategy family G)| ≤ Real.sqrt zeta := by
  have hdef :
      evaluatedSlicePhaseTwoStabilityDefect params strategy family G =
        gCommStabilityScalarDefect params strategy family G := by
    funext y
    rfl
  rw [hdef]
  exact gCommStability_scalar params strategy zeta hnorm family G hG hbound
















end MIPStarRE.LDT.Commutativity

end

/- Source helpers from MIPStarRE/LDT/Preliminaries/CauchySchwarz.lean. -/
/-!
# Cauchy–Schwarz Inequalities for Approximate Measurements

Formalizes Cauchy–Schwarz-style propositions from Section 3
(Preliminaries) of the LDT paper:
- `easyApproxFromApproxDelta` — Proposition `prop:easy-approx-from-approx-delta`
- `closenessOfIP` / `closenessOfIPAdjoint` — Proposition `prop:closeness-of-ip`
  (`eq:closeness3` / `eq:closeness4`)
- `cabApproxDelta` — Proposition `prop:cab-approx-delta`

## References

- `references/ldt-paper/preliminaries.tex`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT







/-- `prop:closeness-of-ip` (`eq:closeness3`).

If `A ≈_γ B` (raw matrices) and `Σ_a (Σ_b C_{a,b})(Σ_b C_{a,b})† ≤ I`,
then
`|𝔼_x Σ_{a,b} ⟨ψ| C_{a,b} A_a |ψ⟩ -
  𝔼_x Σ_{a,b} ⟨ψ| C_{a,b} B_a |ψ⟩| ≤ √γ`. -/
theorem closenessOfIP
    {Question OutcomeA OutcomeB : Type*} {ι : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (γ : Error)
    (hAB : avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q)) ≤ γ)
    (hC :
      ∀ q,
        ∑ a : OutcomeA,
          (∑ b : OutcomeB, C q a b) * (∑ b : OutcomeB, C q a b)ᴴ ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a))| ≤
      Real.sqrt γ := by
  simpa using closenessOfInnerProduct_left ψ hψ 𝒟 h𝒟 A B C γ hAB hC





end MIPStarRE.LDT.Preliminaries

end

end LIDT

open LIDT
/-!
# Main scalar chain assembly

The core lemma `evaluatedSlice_scalar_chain_bound` that assembles the ten-step
scalar approximation chain for `lem:comm-data-processed-g`.  This is the
heavyweight proof corresponding to `references/ldt-paper/commutativity-G.tex`,
lines 72–131.  Phases 1, 3, 4, 6–7, and 8–9 are supplied by the reverse and
tail parts of the paper chain; Phase 2 uses the reindexing infrastructure from
`PhaseTwo`.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]











/- Scalar approximation chain for the evaluated-slice commutation.

This is the core of the paper's proof of `lem:comm-data-processed-g`
(`references/ldt-paper/commutativity-G.tex`, lines 72–131).
Starting from `E[∑ ABAB]`, the proof applies ten approximation steps:

1. `≈_{2√ζ}`: insert Bob's measurement via `closenessOfIP` + `eq:add-an-a`
2. `≈_{√ζ}`: remove trailing `G^y` (`clm:g-comm-stability`)
3. `≈_{2√ζ}`: insert Bob's second measurement via `closenessOfIP` +
   `eq:add-an-a`
4. `≈_{6√(γ(m+1))}`: swap Bob's measurements via `closenessOfIP` +
   `commutativityPoints`
5a. `≈_{6√(γ(m+1))}`: the point-measurement swap contribution internal
    to the paper's `clm:g-comm-stability2` accounting
5b. `≈_{√ζ}`: remove trailing `G^x` by the boundedness part of
    `gCommStabilityTwo_raw_scalar` (this is the scalar part of `hphase5paper` below)
6–7. `≈_{2√ζ + 2√ζ}`: reverse the `eq:add-an-a` insertions
8–9. `≈_{√ζ + √ζ}`: apply postprocessed self-consistency twice

Summing: `Σεᵢ = 12√ζ + 12√(γ(m+1))`, so `2 * Σεᵢ ≤ 48m(√γ + √ζ)`. -/

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (_hnorm : strategy.state.IsNormalized)
    (_hcomm :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.GlobalVariance.PointPairQuestion params.next))
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductLeft params.next strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductRight params.next strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params.next gamma))
    (_hgamma_nonneg : 0 ≤ gamma)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (G : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ι)
    (_hG : ∀ x, G x = (family.meas x).toSubMeas)
    (_hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (_hpostSSC : _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft params family)
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyRight params family)
      zeta) :
    2 *
      (_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm params strategy family q ab) -
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab)) ≤
      _root_.LIDT.MIPStarRE.LDT.Commutativity.commDataProcessedGError params gamma zeta := by
  -- Paper reference: commutativity-G.tex, proof of lem:comm-data-processed-g,
  -- equations (eq:gcom8) through the final displayed error estimate.
  -- Each step uses closenessOfIP, easyApproxFromApproxDelta, or the
  -- stability claims (clm:g-comm-stability, clm:g-comm-stability2).
  -- The algebraic qSDDOp expansions and stability families are defined
  -- in Commutativity/Defs.lean; the Cauchy-Schwarz bridges are in
  -- Preliminaries/CauchySchwarz.lean.
  have h𝒟 :
      ∑ q ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)).support,
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)).weight q ≤ 1 := by
    simpa using
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
  have hpostSSC_fst :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointSelfConsistency_fst params strategy family zeta _hpostSSC
  have hpostSSC_snd :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointSelfConsistency_snd params strategy family zeta _hpostSSC
  let 𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params) :=
    _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
  let avgABAB : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab
  let avgABA : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm params strategy family q ab
  let avgBAB : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABTerm params strategy family q ab
  let pointMeas : _root_.LIDT.MIPStarRE.LDT.IdxMeas (_root_.LIDT.MIPStarRE.LDT.Point params.next) (_root_.LIDT.MIPStarRE.LDT.Fq params) ι :=
    fun u => by
      simpa [_root_.LIDT.MIPStarRE.LDT.Parameters.next] using (strategy.pointMeasurement u).toMeasurement
  have hcons_swapped :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily_pointConsistency_swapped params strategy family zeta _hcons
  have hconsSub :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.consSubMeas
      strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
      pointMeas
      zeta
      hcons_swapped
  have hcombined_snd :
      _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft params family q.2)
        (fun q =>
          (_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
            pointMeas q.2))
        (4 * zeta) := by
    rcases hconsSub.combinedControl with ⟨h⟩
    constructor
    simpa [_root_.LIDT.MIPStarRE.LDT.sddError, _root_.LIDT.MIPStarRE.LDT.qSDD, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft, _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft,
      _root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas] using
      (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_snd (α := _root_.LIDT.MIPStarRE.LDT.Point params.next) (β := _root_.LIDT.MIPStarRE.LDT.Point params.next)
        (f := fun u =>
          _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
            ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)) u)
            ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
              pointMeas u)))).trans_le h
  have hcombined_fst :
      _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft params family q.1)
        (fun q =>
          (_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
            pointMeas q.1))
        (4 * zeta) := by
    rcases hconsSub.combinedControl with ⟨h⟩
    constructor
    simpa [_root_.LIDT.MIPStarRE.LDT.sddError, _root_.LIDT.MIPStarRE.LDT.qSDD, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft, _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft,
      _root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas] using
      (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_fst (α := _root_.LIDT.MIPStarRE.LDT.Point params.next) (β := _root_.LIDT.MIPStarRE.LDT.Point params.next)
        (f := fun u =>
          _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
            ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)) u)
            ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
              pointMeas u)))).trans_le h
  let phase1Inserted : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
      _root_.LIDT.MIPStarRE.LDT.ev strategy.state
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a)) *
          ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy) q.2).outcome b))
  let phase3Inserted : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
      _root_.LIDT.MIPStarRE.LDT.ev strategy.state
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b)) *
          ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy) q.1).outcome a))
  let phase2Removed : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
      _root_.LIDT.MIPStarRE.LDT.ev strategy.state
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a)) *
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b))
  -- Paper line 86: insert the first-coordinate point measurement after `gcom9`.
  -- Unfolding `totalSandwichFamily`, this is the average of
  -- `G^{u,x}_a G^{v,y}_b G^x ⊗ A^{v,y}_b A^{u,x}_a`.
  let phase3PaperInserted : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
      _root_.LIDT.MIPStarRE.LDT.ev strategy.state
        ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b)) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b)) *
          ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy) q.1).outcome a))
  -- Paper line 87: swap the two right-register point measurements.
  let phase4PaperSwapped : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
      _root_.LIDT.MIPStarRE.LDT.ev strategy.state
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).total) *
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
            (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a) *
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b)))
  -- Paper line 87 after removing the trailing first-slice total `G^x`.
  let phase5PaperRemoved : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperRemoved params strategy family
  -- Paper lines 101--119 endpoints for the reverse insertions and tail.
  let phase7GonnaCite : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseSevenGonnaCite params strategy family
  let phase8TailRight : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseEightTailRight params strategy family
  -- Phase 1: `eq:gcom8 -> eq:apply-add-an-a-once`.
  have hphase1 :
      |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgABAB - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase1Inserted| ≤ 2 * Real.sqrt zeta := by
    simpa [𝒟, avgABAB, phase1Inserted] using
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseOne_insert_bound
        params strategy zeta _hnorm family hcombined_snd
  -- Phase 2: remove the trailing `G^y` from the phase-1 inserted term via the
  -- direct boundedness estimate `gCommStability_scalar`.
  -- The analytic part is closed by `evaluatedSlice_phaseTwo_stability_defect_bound`,
  -- the sign/algebra expansion is proved by
  -- `evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect`, and the finite
  -- marginalization below identifies the question-level defect with
  -- `evaluatedSlicePhaseTwoStabilityDefect`: decompose the sampled second point as
  -- `(v,y)`, collapse the postprocessing fibers `∑_b ∑_{g : g(v)=b}` to `∑_g`,
  -- then average the first sampled point into `gCommStabilityR`.
  have hphase2 :
      |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase1Inserted - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase2Removed| ≤ Real.sqrt zeta := by
    have hdefect :=
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseTwo_stability_defect_bound
        params strategy zeta _hnorm family G _hG _hbound
    have hsign :
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase1Inserted - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase2Removed =
          -_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoQuestionDefect params strategy family G) := by
      simpa [𝒟, phase1Inserted, phase2Removed] using
        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect
          params strategy family G _hG
    have hbridge :
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoQuestionDefect params strategy family G) =
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoStabilityDefect params strategy family G) := by
      simpa [𝒟] using
        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseTwo_questionDefect_avg_eq_stabilityDefect
          params strategy family G
    have hrewrite :
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase1Inserted - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase2Removed =
          -_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoStabilityDefect params strategy family G) := by
      calc
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase1Inserted - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase2Removed
            = -_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
                (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoQuestionDefect params strategy family G) := hsign
        _ = -_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
                (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoStabilityDefect params strategy family G) := by
              rw [hbridge]
    calc
      |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase1Inserted - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase2Removed|
          = |-(_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoStabilityDefect params strategy family G))| := by
              rw [hrewrite]
      _ = |_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoStabilityDefect params strategy family G)| := by
              rw [abs_neg]
      _ ≤ Real.sqrt zeta := hdefect
  -- Paper line 86, first approximation: insert the first-coordinate
  -- `G^x \otimes A^{u,x}_a` endpoint into the post-`gcom9` expression.
  have hphase3paper :
      |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase2Removed - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase3PaperInserted| ≤
        2 * Real.sqrt zeta := by
    let A : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
      fun q a => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a)
    let B : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
      fun q a =>
        ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy) q.1).outcome a)
    let C : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.Fq params →
        _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
      fun q a b =>
        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b)) *
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
            ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b)
    have hAB :
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (A q) (B q)) ≤ 4 * zeta := by
      have hbound := hcombined_fst.squaredDistanceBound
      change _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (A q) (B q)) ≤
        4 * zeta at hbound
      exact hbound
    have hC :
        ∀ q, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, (∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, C q a b) * (∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, C q a b)ᴴ ≤ 1 := by
      intro q
      simpa [C, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas, _root_.LIDT.MIPStarRE.LDT.Parameters.next] using
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.leftRightTensor_prefix_pointMeasurement_normalization
          (A := _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q)
          (B := _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q)
          (R := strategy.pointMeasurement q.2))
    have hremoved :
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase2Removed =
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C q a b * A q a)) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      intro q
      dsimp [phase2Removed, A, C]
      rw [Finset.sum_comm]
      simp [_root_.LIDT.MIPStarRE.LDT.opTensor_mul, mul_assoc]
    have hinserted :
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase3PaperInserted =
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C q a b * B q a)) := by
      rfl
    have hclose :=
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.closenessOfIP
        strategy.state _hnorm 𝒟 h𝒟 A B C (4 * zeta) hAB hC
    calc
      |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase2Removed - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase3PaperInserted|
          = |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C q a b * A q a)) -
            _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C q a b * B q a))| := by
              rw [hremoved, hinserted]
      _ ≤ Real.sqrt (4 * zeta) := hclose
      _ = 2 * Real.sqrt zeta := by
            rw [Real.sqrt_mul (show 0 ≤ (4 : _root_.LIDT.MIPStarRE.LDT.Error) by positivity)]
            norm_num
  -- Paper line 87: commute the two right-register point measurements.
  -- The `6√(γ(m+1))` bound comes from `commutativityPoints` via `closenessOfIP`:
  -- the SDDOpRel error is `32·γ·(m+1)`, applying `closenessOfIP` gives
  -- `√(32·γ·(m+1))`, and `√32 ≤ 6` rounds up to match the paper's constant.
  have hphase4paper :
      |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase3PaperInserted - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase4PaperSwapped| ≤
        6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    let C : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params →
        _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
      evaluatedSlicePointSwapRightPrefix (ι := ι) params family (fun q =>
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).total)
    have hC :
        ∀ q, ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params, C q ab * (C q ab)ᴴ ≤ 1 := by
      simpa [C] using
        evaluatedSlice_pointSwap_right_prefix_normalization
          (ι := ι) params family
          (fun q => (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).total)
          (fun q => (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).total_nonneg)
          (fun q => (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).total_le_one)
    have hphase3_norm :
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase3PaperInserted =
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (C q ab *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                  (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
                    ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      intro q
      calc
        phase3PaperInserted q =
            ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (C q (a, b) *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                    (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b) *
                      ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a))) := by
              dsimp [phase3PaperInserted, C, evaluatedSlicePointSwapRightPrefix]
              refine Finset.sum_congr rfl ?_
              intro a _
              refine Finset.sum_congr rfl ?_
              intro b _
              congr 1
              simp [_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily,
                _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor, _root_.LIDT.MIPStarRE.LDT.opTensor_mul, mul_assoc]
        _ = ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (C q ab *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                    (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
                      ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome ab.1))) := by
              simpa using
                (Fintype.sum_prod_type' (f := fun a : _root_.LIDT.MIPStarRE.LDT.Fq params => fun b : _root_.LIDT.MIPStarRE.LDT.Fq params =>
                  _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                    (C q (a, b) *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                        (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b) *
                          ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a))))).symm
    have hphase4_norm :
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase4PaperSwapped =
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (C q ab *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                  (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
                    ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      intro q
      dsimp [phase4PaperSwapped, C, evaluatedSlicePointSwapRightPrefix]
      simpa using
        (Fintype.sum_prod_type' (f := fun a : _root_.LIDT.MIPStarRE.LDT.Fq params => fun b : _root_.LIDT.MIPStarRE.LDT.Fq params =>
          _root_.LIDT.MIPStarRE.LDT.ev strategy.state
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                  ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
                  (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).total) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a) *
                  ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b))))).symm
    exact
      evaluatedSlice_pointSwap_right_bound_of_norms
        params strategy gamma _hnorm _hcomm C hC
        phase3PaperInserted phase4PaperSwapped hphase3_norm hphase4_norm
  -- Paper phase five: remove the trailing `G^x` total from the line-87 endpoint.
  -- The `√ζ + 6√(γ(m+1))` bound decomposes as:
  --   - `√ζ` from `gCommStabilityTwo_raw_scalar` (the boundedness part of
  --     `clm:g-comm-stability2`, corresponding to the paper's line 93 `≈_{√ζ}`)
  --   - `6√(γ(m+1))` from swapping the right-register point measurements
  --     inside the phase-5 defect (same `commutativityPoints` →
  --     `closenessOfIP` → `√32 ≤ 6` chain as Phase 4).
  -- The ordered defect is first swapped on the right register, then reindexed to
  -- `gCommStabilityTwoRawScalarDefect`, whose average is controlled by the new
  -- raw scalar stability theorem.
  have hphase5paper :
      |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase4PaperSwapped - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase5PaperRemoved| ≤
        Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    let orderedDefect : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error :=
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperOrderedDefect params strategy family G
    let swappedDefect : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error :=
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G
    have hsign :
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase4PaperSwapped - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase5PaperRemoved =
          -_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 orderedDefect := by
      simpa [𝒟, phase4PaperSwapped, phase5PaperRemoved, orderedDefect] using
        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseFivePaper_avg_diff_eq_neg_orderedDefect
          params strategy family G _hG
    have hraw : |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 swappedDefect| ≤ Real.sqrt zeta := by
      have hraw0 :=
        _root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityTwo_raw_scalar
          params strategy zeta _hnorm family G _hG _hbound
      have hreindex :
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 swappedDefect =
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityTwoRawScalarDefect params strategy family G) := by
        simpa [𝒟, swappedDefect] using
          _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseFivePaper_reindex_to_raw_defect
            params strategy family G _hG
      calc
        |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 swappedDefect|
            = |_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
                (_root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityTwoRawScalarDefect params strategy family G)| := by
              rw [hreindex]
        _ ≤ Real.sqrt zeta := hraw0
    have hswap_defect :
        |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 orderedDefect - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 swappedDefect| ≤
          6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) := by
      let C : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params →
          _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
        evaluatedSlicePointSwapRightPrefix (ι := ι) params family (fun q =>
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) - (G (_root_.LIDT.MIPStarRE.LDT.pointHeight params q.1)).total)
      have hT_nonneg : ∀ q : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params,
          0 ≤ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) - (G (_root_.LIDT.MIPStarRE.LDT.pointHeight params q.1)).total := by
        intro q
        exact sub_nonneg.mpr (G (_root_.LIDT.MIPStarRE.LDT.pointHeight params q.1)).total_le_one
      have hT_le_one : ∀ q : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params,
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) - (G (_root_.LIDT.MIPStarRE.LDT.pointHeight params q.1)).total ≤ 1 := by
        intro q
        simpa using
          (sub_le_self (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)
            (G (_root_.LIDT.MIPStarRE.LDT.pointHeight params q.1)).total_nonneg)
      have hC :
          ∀ q, ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params, C q ab * (C q ab)ᴴ ≤ 1 := by
        simpa [C] using
          evaluatedSlice_pointSwap_right_prefix_normalization
            (ι := ι) params family
            (fun q => (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) - (G (_root_.LIDT.MIPStarRE.LDT.pointHeight params q.1)).total)
            hT_nonneg hT_le_one
      have hord_norm :
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 orderedDefect =
            _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (C q ab *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                    (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
                      ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))) := by
        apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
        intro q
        dsimp [orderedDefect, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperOrderedDefect, C,
          evaluatedSlicePointSwapRightPrefix]
        simpa using
          (Fintype.sum_prod_type' (f := fun a : _root_.LIDT.MIPStarRE.LDT.Fq params => fun b : _root_.LIDT.MIPStarRE.LDT.Fq params =>
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                  (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                    ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
                    (1 - (G (_root_.LIDT.MIPStarRE.LDT.pointHeight params q.1)).total)) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                  (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a) *
                    ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b))))).symm
      have hswap_norm :
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 swappedDefect =
            _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (C q ab *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                    (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
                      ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))) := by
        apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
        intro q
        dsimp [swappedDefect, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperSwappedDefect, C,
          evaluatedSlicePointSwapRightPrefix]
        simpa using
          (Fintype.sum_prod_type' (f := fun a : _root_.LIDT.MIPStarRE.LDT.Fq params => fun b : _root_.LIDT.MIPStarRE.LDT.Fq params =>
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                  (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                    ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
                    (1 - (G (_root_.LIDT.MIPStarRE.LDT.pointHeight params q.1)).total)) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                  (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b) *
                    ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a))))).symm
      have hswap :=
        evaluatedSlice_pointSwap_right_bound_of_norms
          params strategy gamma _hnorm _hcomm C hC
          swappedDefect orderedDefect hswap_norm hord_norm
      simpa [abs_sub_comm] using hswap
    have hordered_abs :
        |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 orderedDefect| ≤
          Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) := by
      calc
        |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 orderedDefect|
            = |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 orderedDefect - 0| := by simp
        _ ≤ |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 orderedDefect - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 swappedDefect| +
              |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 swappedDefect - 0| :=
                abs_sub_le (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 orderedDefect) (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 swappedDefect) 0
        _ ≤ 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) + Real.sqrt zeta := by
                exact add_le_add hswap_defect (by simpa using hraw)
        _ = Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) := by
                ring
    calc
      |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase4PaperSwapped - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase5PaperRemoved|
          = |-(_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 orderedDefect)| := by
              rw [hsign]
      _ = |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 orderedDefect| := by rw [abs_neg]
      _ ≤ Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) :=
              hordered_abs
  -- Paper lines 99--104: reverse the two `eq:add-an-a` insertions.
  have hphase67paper :
      |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase5PaperRemoved - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase7GonnaCite| ≤
        4 * Real.sqrt zeta := by
    simpa [𝒟, phase5PaperRemoved, phase7GonnaCite] using
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseSixSeven_reverse_bound
        params strategy zeta _hnorm family hcombined_fst hcombined_snd
  -- Paper line 117--118: first postprocessed self-consistency tail move.
  have htail8 :
      |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase7GonnaCite - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase8TailRight| ≤ Real.sqrt zeta := by
    simpa [𝒟, phase7GonnaCite, phase8TailRight] using
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseEight_tail_bound
        params strategy zeta _hnorm family hpostSSC_snd
  -- Paper line 118--119: move that same second-coordinate factor back to the left.
  have htail9 :
      |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase8TailRight - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgBAB| ≤ Real.sqrt zeta := by
    simpa [𝒟, phase8TailRight, avgBAB] using
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseNine_tail_bound
        params strategy zeta _hnorm family hpostSSC_snd
  -- ── Final assembly (hassemble) ────────────────────────────────────────────
  -- The paper chain (commutativity-G.tex, lines 72–119) converts `ABAB` to `ABA`
  -- through ten approximation steps.  In the Lean development, the chain
  -- terminates at `BAB` after Phase 4, then we apply the exact swap-symmetry
  -- identity `avgBAB = avgABA`.  This identity is an equality, not an
  -- approximation: the uniform average over evaluated-slice questions is
  -- invariant under swapping the question coordinates `(q₁,q₂)↦(q₂,q₁)`, and
  -- the corresponding relabeling of outcomes `(a,b)↦(b,a)` transforms the
  -- `BAB` term into the `ABA` term.  See
  -- `EvaluatedSliceCommutation/Averages.lean` for the proof.
  have hassemble :
      2 * (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgABA - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgABAB) ≤
        _root_.LIDT.MIPStarRE.LDT.Commutativity.commDataProcessedGError params gamma zeta := by
    have hswap := _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceCommutation_avg_swap_terms params strategy family
    have hBABeqABA : _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgBAB = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgABA := hswap.1
    have hγζ_chain :
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgBAB - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgABAB ≤
          12 * Real.sqrt zeta +
            12 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) := by
      have h01 : _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase1Inserted - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgABAB ≤
          2 * Real.sqrt zeta := by
        exact le_trans (le_abs_self _)
          ((abs_sub_comm (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase1Inserted) (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgABAB)).symm ▸ hphase1)
      have h12 : _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase2Removed - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase1Inserted ≤
          Real.sqrt zeta := by
        exact le_trans (le_abs_self _)
          ((abs_sub_comm (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase2Removed) (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase1Inserted)).symm ▸ hphase2)
      have h23 : _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase3PaperInserted - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase2Removed ≤
          2 * Real.sqrt zeta := by
        have h :=
          (abs_sub_comm (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase3PaperInserted)
            (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase2Removed)).symm ▸ hphase3paper
        exact le_trans (le_abs_self _) h
      have h34 : _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase4PaperSwapped - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase3PaperInserted ≤
          6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) := by
        have h :=
          (abs_sub_comm (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase4PaperSwapped)
            (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase3PaperInserted)).symm ▸ hphase4paper
        exact le_trans (le_abs_self _) h
      have h45 : _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase5PaperRemoved - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase4PaperSwapped ≤
          Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) := by
        have h :=
          (abs_sub_comm (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase5PaperRemoved)
            (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase4PaperSwapped)).symm ▸ hphase5paper
        exact le_trans (le_abs_self _) h
      have h57 : _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase7GonnaCite - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase5PaperRemoved ≤
          4 * Real.sqrt zeta := by
        have h :=
          (abs_sub_comm (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase7GonnaCite)
            (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase5PaperRemoved)).symm ▸ hphase67paper
        exact le_trans (le_abs_self _) h
      have h78 : _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase8TailRight - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase7GonnaCite ≤
          Real.sqrt zeta := by
        exact le_trans (le_abs_self _)
          ((abs_sub_comm (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase8TailRight) (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase7GonnaCite)).symm ▸ htail8)
      have h89 : _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgBAB - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase8TailRight ≤
          Real.sqrt zeta := by
        exact le_trans (le_abs_self _)
          ((abs_sub_comm (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgBAB) (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase8TailRight)).symm ▸ htail9)
      linarith
    have hmain_one :
        2 * (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgABA - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgABAB) ≤
          24 * Real.sqrt zeta +
            24 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) := by
      have hrw : _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgABA - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgABAB =
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgBAB - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgABAB := by
        linarith
      rw [hrw]
      nlinarith
    have hgamma_nonneg : 0 ≤ gamma := by
      exact _hgamma_nonneg
    have hzeta_nonneg : 0 ≤ zeta :=
      le_trans (_root_.LIDT.MIPStarRE.LDT.sddError_nonneg strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft params family)
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyRight params family)) _hpostSSC.squaredDistanceBound
    have hm : 1 ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by exact_mod_cast params.hm
    have hsqrtn_le :
        Real.sqrt ((((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ 2 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
      rw [Real.sqrt_le_iff]
      constructor
      · nlinarith
      · norm_num
        nlinarith
    have hgamma_tail :
        Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
          2 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Real.sqrt gamma := by
      rw [Real.sqrt_mul hgamma_nonneg]
      calc
        Real.sqrt gamma * Real.sqrt ((((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error))
            ≤ Real.sqrt gamma * (2 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error)) := by
              exact mul_le_mul_of_nonneg_left hsqrtn_le (Real.sqrt_nonneg gamma)
        _ = 2 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Real.sqrt gamma := by ring
    have htarget_sqrt :
        24 * Real.sqrt zeta +
            24 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
          48 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * (Real.sqrt gamma + Real.sqrt zeta) := by
      have hzpart : 24 * Real.sqrt zeta ≤
          48 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Real.sqrt zeta := by
        have hzsqrt_nonneg : 0 ≤ Real.sqrt zeta := Real.sqrt_nonneg _
        nlinarith
      have hgpart : 24 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
          48 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Real.sqrt gamma := by
        nlinarith
      nlinarith
    calc
      2 * (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgABA - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgABAB)
          ≤ 24 * Real.sqrt zeta +
            24 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) := hmain_one
      _ ≤ 48 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * (Real.sqrt gamma + Real.sqrt zeta) := htarget_sqrt
      _ = _root_.LIDT.MIPStarRE.LDT.Commutativity.commDataProcessedGError params gamma zeta := by
        unfold _root_.LIDT.MIPStarRE.LDT.Commutativity.commDataProcessedGError
        rw [Real.sqrt_eq_rpow gamma, Real.sqrt_eq_rpow zeta]
        rfl
  simpa [𝒟, avgABA, avgABAB] using hassemble
