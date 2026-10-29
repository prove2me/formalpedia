-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.twisted_commutation_of_halves
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:51:21.24606+00:00
-- url     : https://prove2.me/submissions/49c554f6-b848-47b1-a41e-d94bc4cf4f46

-- Generated proof for MIPStarRE.QPBT.WinImplications.twisted_commutation_of_halves.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_TwistedCommutation
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_avgOver_uniform_split_le
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_norm_twistedCommutator_sq_le_four

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Observables/WinImplications/AnticommutingObs.lean. -/
/-!
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reading the dilation back on the original space -/













/-! ## The Magic Square anticommutation on the undilated strategy -/













/-! ## Reflections and the product transfer -/











/-! ## From the Magic Square variables to the point observables -/









/-! ## The anticommuting half of the twisted commutation -/

/-- The unit-alphabet operator distance written as an average of squared
state-dependent norms. Formalization-only support for `def:povm-distance`,
blueprint `ch12_qpbt_games.tex:234-241`. -/
theorem opDistSq_eq_avgOver {X ι : Type*} [Fintype X] [DecidableEq X]
    [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (M N : X → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opDistSq μ M N ψ =
      _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ‖_root_.MIPStarRE.QPBT.applyOperatorToState (M x - N x) ψ‖ ^ 2) := by
  unfold _root_.MIPStarRE.QPBT.opDistSq _root_.MIPStarRE.QPBT.opFamilyDistSq
  simp



















end WinImplications

end

end MIPStarRE.QPBT

/-!
# The phase-signed commutation relation of the point observables

This module assembles the commuting and anticommuting halves into Equation
`eq:pts-obs-commutation` of `lem:qld-win-implications-obs`: on average over a
uniformly random tuple the two point observables commute up to the sign
`(-1)^gamma(omega)`, with error the square root of the test error.

## References

The declarations formalize the first assertion of
`lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-362`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications



/-! ## The unconditional bound on a difference of reflections -/





/-! ## Splitting the uniform average -/









/-! ## The twisted commutation relation -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyTwisted

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ιL ιR : Type}
    [Fintype ιL] [DecidableEq ιL] [Fintype ιR] [DecidableEq ιR]
    (OX OZ : _root_.MIPStarRE.QPBT.PauliTuple P → _root_.LIDT.MIPStarRE.Quantum.Op ιL) (χ : EuclideanSpace ℂ (ιL × ιR))
    (hχ : ‖χ‖ = 1) (hOX : ∀ ω, (OX ω)ᴴ * OX ω = 1)
    (hOZ : ∀ ω, (OZ ω)ᴴ * OZ ω = 1) {ε Cc Ca : ℝ}
    (hε : 0 ≤ ε) (hCc : 0 ≤ Cc) (hCa : 0 ≤ Ca)
    (hcomm : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.commTupleDist P) (fun ω =>
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (OX ω * OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
        _root_.MIPStarRE.QPBT.heteroKron (OZ ω * OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ‖ ^ 2) ≤
        Cc * (ε + Real.sqrt ε))
    (hanti : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) (fun ω =>
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (OX ω * OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) +
        _root_.MIPStarRE.QPBT.heteroKron (OZ ω * OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ‖ ^ 2) ≤ Ca * ε) :
    _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P))
      (fun ω => _root_.MIPStarRE.QPBT.heteroKron (OX ω * OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR))
      (fun ω => _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
        _root_.MIPStarRE.QPBT.heteroKron (OZ ω * OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ ≤
      (2 * Cc + Ca + 4) * Real.sqrt ε := by
  classical
  rw [_root_.MIPStarRE.QPBT.WinImplications.opDistSq_eq_avgOver]
  set f : _root_.MIPStarRE.QPBT.PauliTuple P → ℝ := fun ω =>
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (OX ω * OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
      _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
        _root_.MIPStarRE.QPBT.heteroKron (OZ ω * OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ‖ ^ 2 with hfdef
  have hfnn : ∀ ω, 0 ≤ f ω := by
    intro ω
    rw [hfdef]
    positivity
  have hsq : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hcbound : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.commTupleDist P) f ≤ Cc * (ε + Real.sqrt ε) := by
    refine le_trans (le_of_eq ?_) hcomm
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr_on_support _ _ _ ?_
    intro ω hω
    have hIs : _root_.MIPStarRE.QPBT.IsCommuting ω := by
      rw [_root_.MIPStarRE.QPBT.commTupleDist, _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset_support,
        Finset.mem_filter] at hω
      exact hω.2
    have hph : _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) = 1 := by
      rw [show _root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = 0 from hIs]
      simp [_root_.MIPStarRE.QPBT.phaseSign]
    simp only [hfdef]
    rw [hph, one_smul]
  have habound : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) f ≤ Ca * ε := by
    refine le_trans (le_of_eq ?_) hanti
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr_on_support _ _ _ ?_
    intro ω hω
    have hIs : _root_.MIPStarRE.QPBT.IsAnticommuting ω := by
      rw [_root_.MIPStarRE.QPBT.anticommTupleDist, _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset_support,
        Finset.mem_filter] at hω
      exact hω.2
    have hone : _root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = 1 := by
      have h := hIs
      rw [_root_.MIPStarRE.QPBT.IsAnticommuting] at h
      revert h
      generalize _root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = t
      revert t
      decide
    have hph : _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) = -1 := by
      rw [hone]
      simp [_root_.MIPStarRE.QPBT.phaseSign, show (1 : ZMod 2) ≠ 0 from by decide]
    simp only [hfdef]
    rw [hph, neg_one_smul, sub_neg_eq_add]
  have hmain : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P)) f ≤
      Cc * (ε + Real.sqrt ε) + Ca * ε :=
    _root_.MIPStarRE.QPBT.WinImplications.avgOver_uniform_split_le P f hfnn hcbound habound
  have htriv : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P)) f ≤ 4 := by
    refine le_trans (_root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ (fun _ => (4 : ℝ)) ?_) ?_
    · intro ω
      rw [hfdef]
      exact _root_.MIPStarRE.QPBT.WinImplications.norm_twistedCommutator_sq_le_four OX OZ χ hχ hOX hOZ ω
    · exact le_of_eq (_root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability _
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability (_root_.MIPStarRE.QPBT.PauliTuple P)) 4)
  by_cases hle : ε ≤ 1
  · have hsle : Real.sqrt ε ≤ 1 := by nlinarith [Real.sq_sqrt hε]
    have hεsq : ε ≤ Real.sqrt ε := by nlinarith [Real.sq_sqrt hε]
    have h1 : Cc * (ε + Real.sqrt ε) + Ca * ε ≤
        (2 * Cc + Ca) * Real.sqrt ε := by
      nlinarith [mul_le_mul_of_nonneg_left hεsq hCc,
        mul_le_mul_of_nonneg_left hεsq hCa]
    have h2 : (2 * Cc + Ca) * Real.sqrt ε ≤
        (2 * Cc + Ca + 4) * Real.sqrt ε := by nlinarith [hsq]
    linarith
  · have hgt : (1 : ℝ) < ε := not_le.mp hle
    have hone : (1 : ℝ) ≤ Real.sqrt ε := by
      nlinarith [Real.sq_sqrt hε, Real.sqrt_nonneg ε]
    have h3 : (4 : ℝ) ≤ (2 * Cc + Ca + 4) * Real.sqrt ε := by
      nlinarith [hone, hCc, hCa]
    linarith
