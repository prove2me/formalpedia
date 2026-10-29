-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MainInductionStep.min_eps_one_le_mainInductionError_of_m_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:37:59.459952+00:00
-- url     : https://prove2.me/submissions/a2878587-4460-4d12-b372-a337f212243d

-- Generated proof for MIPStarRE.LDT.MainInductionStep.min_eps_one_le_mainInductionError_of_m_eq_one.
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

/- Source helpers from MIPStarRE/LDT/MainInductionStep/Theorems/InductionParameterBounds/Preliminaries.lean. -/
/-!
# Section 6 — Induction Parameter Bound Preliminaries

This file is one leaf of `InductionParameterBounds`. It contains the elementary
point-line reduction for the base case, the real-variable comparison lemmas used
by the small-parameter estimates, and the bound `d/q ≤ 1`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



lemma min_le_rpow_of_nonneg_of_exponent_le_one {x c : Error}
    (hx : 0 ≤ x) (hc_nonneg : 0 ≤ c) (hc_le_one : c ≤ 1) :
    min x 1 ≤ Real.rpow x c := by
  by_cases hx1 : x ≤ 1
  · rw [min_eq_left hx1]
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hx hx1 hc_nonneg hc_le_one)
  · rw [min_eq_right (le_of_not_ge hx1)]
    simpa using Real.rpow_le_rpow (by positivity) (le_of_not_ge hx1) hc_nonneg







end MIPStarRE.LDT.MainInductionStep

end

end LIDT

open LIDT
/-!
# Section 6 — Induction Parameter Bound Preliminaries

This file is one leaf of `InductionParameterBounds`. It contains the elementary
point-line reduction for the base case, the real-variable comparison lemmas used
by the small-parameter estimates, and the bound `d/q ≤ 1`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (k : ℕ) (eps delta gamma : _root_.LIDT.MIPStarRE.LDT.Error)
    (hm1 : params.m = 1)
    (heps_nonneg : 0 ≤ eps) (hdelta_nonneg : 0 ≤ delta) (hgamma_nonneg : 0 ≤ gamma) :
    min eps 1 ≤ _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params k eps delta gamma := by
  by_cases hk0 : k = 0
  · subst hk0
    simp [_root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError, _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionNu, hm1]
  · have hmin : min eps 1 ≤ Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
      _root_.LIDT.MIPStarRE.LDT.MainInductionStep.min_le_rpow_of_nonneg_of_exponent_le_one heps_nonneg (by positivity)
        (by norm_num : (1 / (1024 : Error)) ≤ 1)
    have hother_nonneg :
        0 ≤ Real.rpow delta (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow gamma (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
      have hratio_nonneg : 0 ≤ ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) := by positivity
      have hdelta_rpow_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
        Real.rpow_nonneg hdelta_nonneg _
      have hgamma_rpow_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
        Real.rpow_nonneg hgamma_nonneg _
      have hratio_rpow_nonneg :
          0 ≤ Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
        Real.rpow_nonneg hratio_nonneg _
      nlinarith
    have hsum_ge :
        Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
          Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
            Real.rpow delta (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
            Real.rpow gamma (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
            Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
      nlinarith
    have hk1 : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
    have hk2 : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) := by
      nlinarith
    have hcoef_nonneg :
        0 ≤ 1000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) := by
      positivity
    have hcoef :
        (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 1000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) := by
      simp [hm1]
      nlinarith
    have hrpow_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
      exact Real.rpow_nonneg heps_nonneg _
    have hmul :
        Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
          1000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
            Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
      simpa using (mul_le_mul_of_nonneg_right hcoef hrpow_nonneg)
    have hsum_mul :
        1000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
            Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
          1000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
            (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow delta (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow gamma (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))) := by
      exact mul_le_mul_of_nonneg_left hsum_ge hcoef_nonneg
    have hexp_nonneg :
        0 ≤ Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ))))) := by
      positivity
    calc
      min eps 1 ≤ Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) := hmin
      _ ≤ 1000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
            Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) := hmul
      _ ≤ 1000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
            (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow delta (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow gamma (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)))
                (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))) := hsum_mul
      _ ≤ 1000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
            (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow delta (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow gamma (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))) +
            Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ))))) := by
            linarith
      _ = _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params k eps delta gamma := by
            simp [_root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError, _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionNu, hm1]
