-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MainInductionStep.answer_three_le_k_sq_mul_next_m_of_hsmall
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:37:59.244766+00:00
-- url     : https://prove2.me/submissions/1bc826b2-e5b2-42bd-8f64-a1b98114f9c0

-- Generated proof for MIPStarRE.LDT.MainInductionStep.answer_three_le_k_sq_mul_next_m_of_hsmall.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_MainError
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_Preliminaries
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
import Mathlib
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Test/StrategyFailures.lean. -/
/-!
# Symmetrized-strategy failure probabilities and test bounds

Failure-probability surrogates and basic low-individual-degree test bounds for
the split strategy interface.
-/

@[expose] public section

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

/-! ### Symmetrized strategies and tested-branch bounds -/

namespace SymStrat









end SymStrat









/-! ### Answer-valued symmetric strategies -/

/-- The answer-valued diagonal-line failure surrogate is nonnegative. -/
theorem answer_diagonalFailureProbability_nonneg
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) :
    0 ≤ strategy.diagonalFailureProbability := by
  unfold AnswerSymStrat.diagonalFailureProbability
  refine mul_nonneg ?_ ?_
  · positivity
  · refine Finset.sum_nonneg ?_
    intro j _
    exact bipartiteConsError_nonneg strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
      (AnswerSymStrat.diagonalLineAnswerFamily strategy j)

/-- A good answer-valued symmetric strategy has a nonnegative axis-parallel
error parameter `ε`. -/
theorem answer_eps_nonneg_of_isGood
    (params : Parameters)
    [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ eps := by
  exact le_trans
    (bipartiteConsError_nonneg strategy.state
      (uniformDistribution (AxisParallelTestSample params))
      (AnswerSymStrat.axisParallelPointAnswerFamily strategy)
      (AnswerSymStrat.axisParallelLineAnswerFamily strategy))
    hgood.axisParallelTest

/-- A good answer-valued symmetric strategy has a nonnegative self-consistency
error parameter `δ`. -/
theorem answer_delta_nonneg_of_isGood
    (params : Parameters)
    [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ delta := by
  exact le_trans
    (bipartiteSSCError_nonneg strategy.state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
    hgood.selfConsistencyTest

/-- A good answer-valued symmetric strategy has a nonnegative diagonal-lines
error parameter `γ`. -/
theorem answer_gamma_nonneg_of_isGood
    (params : Parameters)
    [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ gamma := by
  exact le_trans (answer_diagonalFailureProbability_nonneg params strategy)
    hgood.diagonalLineTest



end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Section 6 — Main-Induction Error Bounds

This file is one leaf of `InductionParameterBounds`. It contains the scalar
consequences of the non-vacuous hypothesis `mainInductionError < 1`, including
the bounds `eps ≤ 1`, `delta ≤ 1`, `gamma ≤ 1`, `params.d ≤ params.q`, and
`mainInductionNu < 1`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





















/-! ### Answer-valued small-error scalar consequences -/

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.AnswerSymStrat params.next ι)
    {eps delta gamma : _root_.LIDT.MIPStarRE.LDT.Error} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params.next k eps delta gamma < 1) :
    (3 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
  have hk1_nat : 1 ≤ k :=
    _root_.LIDT.MIPStarRE.LDT.MainInductionStep.one_le_k_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
  by_cases hk1 : k = 1
  · subst hk1
    by_cases hnext_two : params.next.m = 2
    · have heps_nonneg := _root_.LIDT.MIPStarRE.LDT.answer_eps_nonneg_of_isGood params.next strategy hgood
      have hdelta_nonneg := _root_.LIDT.MIPStarRE.LDT.answer_delta_nonneg_of_isGood params.next strategy hgood
      have hgamma_nonneg := _root_.LIDT.MIPStarRE.LDT.answer_gamma_nonneg_of_isGood params.next strategy hgood
      have hratio_nonneg : 0 ≤ ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) := by
        positivity
      have hnu_nonneg : 0 ≤ _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionNu params.next 1 eps delta gamma := by
        have hsumnn :
            0 ≤ Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
                  Real.rpow delta (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
                  Real.rpow gamma (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
                  Real.rpow (((params.next.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.next.q : _root_.LIDT.MIPStarRE.LDT.Error)))
                    (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
          have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
            Real.rpow_nonneg heps_nonneg (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))
          have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
            Real.rpow_nonneg hdelta_nonneg (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))
          have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
            Real.rpow_nonneg hgamma_nonneg (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))
          have hratio_root_nonneg :
              0 ≤ Real.rpow (((params.next.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.next.q : _root_.LIDT.MIPStarRE.LDT.Error)))
                    (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
            Real.rpow_nonneg hratio_nonneg (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))
          nlinarith [heps_root_nonneg, hdelta_root_nonneg, hgamma_root_nonneg,
            hratio_root_nonneg]
        unfold _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionNu
        exact mul_nonneg (by positivity) hsumnn
      have hnext_two' : (params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) = 2 := by
        exact_mod_cast hnext_two
      have hexp_quarter :
          (1 / 4 : _root_.LIDT.MIPStarRE.LDT.Error) ≤
            Real.exp (-((1 : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * ((params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ))))) := by
        have hbase : (1 / 4 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 1 - (1 / 320000 : _root_.LIDT.MIPStarRE.LDT.Error) := by
          norm_num
        have hexp :
            1 - (1 / 320000 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ Real.exp (-(1 / 320000 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
          simpa using Real.one_sub_le_exp_neg (1 / 320000 : _root_.LIDT.MIPStarRE.LDT.Error)
        calc
          (1 / 4 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 1 - (1 / 320000 : _root_.LIDT.MIPStarRE.LDT.Error) := hbase
          _ ≤ Real.exp (-(1 / 320000 : _root_.LIDT.MIPStarRE.LDT.Error)) := hexp
          _ = Real.exp (-((1 : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * ((params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ))))) := by
                rw [hnext_two']
                norm_num
      have hmain_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params.next 1 eps delta gamma := by
        have hm_sq_eq_four : ((params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) = 4 := by
          nlinarith [hnext_two']
        have hinner :
            (1 / 4 : _root_.LIDT.MIPStarRE.LDT.Error) ≤
              _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionNu params.next 1 eps delta gamma +
                Real.exp (-((1 : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * ((params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ))))) := by
          nlinarith
        calc
          (1 : _root_.LIDT.MIPStarRE.LDT.Error) = ((params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (1 / 4 : _root_.LIDT.MIPStarRE.LDT.Error) := by
              rw [hm_sq_eq_four]
              norm_num
          _ ≤ ((params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
                (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionNu params.next 1 eps delta gamma +
                  Real.exp (-((1 : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * ((params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)))))) := by
                gcongr
          _ = _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params.next 1 eps delta gamma := by
                simp [_root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError]
      have hsmall' : _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params.next 1 eps delta gamma < 1 := by
        simpa using hsmall
      linarith
    · have hmnat : 2 ≤ params.next.m := Nat.succ_le_succ params.hm
      have hnext_ge_three : 3 ≤ params.next.m := by
        omega
      have : (3 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
        exact_mod_cast hnext_ge_three
      simpa using this
  · have hk_ge_two : 2 ≤ k := by
      omega
    have hk_sq_ge_four : (4 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) := by
      have hk_two : (2 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) := by
        exact_mod_cast hk_ge_two
      nlinarith
    have hnext_ge_two : (2 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
      exact_mod_cast Nat.succ_le_succ params.hm
    nlinarith
