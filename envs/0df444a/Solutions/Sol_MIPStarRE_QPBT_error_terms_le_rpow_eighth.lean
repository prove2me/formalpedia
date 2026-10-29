-- Prove2me | solution 1 for MIPStarRE.QPBT.error_terms_le_rpow_eighth
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:59:22.2955+00:00
-- url     : https://prove2.me/submissions/983acbca-deb9-491f-990b-99fbed7d6057

-- Generated proof for MIPStarRE.QPBT.error_terms_le_rpow_eighth.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
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
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/-!
# Closeness estimates for the combined point measurements

Given projective measurements `Q^{x,z}` on each player's expanded local space
that are close to the sandwich POVMs on the placements where they were
constructed, this file assembles the three conclusions of `lem:qld-4-10` on
every pair of opposite placements by the triangle inequality along
`Q ≈ R ≈ M^Z M^X ≈ M^X M^Z` and the cross-placement consistency of the
ordered products.  It also records the bound `4` on the averaged squared
state-dependent distance of two families satisfying `∑ a, (A a)ᴴ * A a ≤ 1`
and `∑ a, (B a)ᴴ * B a ≤ 1` at every question, used when the test error
exceeds one, and the elementary estimate collapsing the error terms `ε`,
`√ε`, and `(ε + √ε)^{1/4}` into a single power `ε^{1/8}` when `ε ≤ 1`.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:838-881`
(self-consistency and consistency with `M̂` in the proof of `lem:qld-4-10`),
blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex:803-960`; the route
is explained in `docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## The trivial bound -/









/-! ## The chain of closeness estimates -/

open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}





/-! ## Collapsing the error terms into one power -/

theorem solution {ε C₀ : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hC₀ : 1 ≤ C₀) :
    ε ≤ Real.rpow ε (1 / 8 : ℝ) ∧ Real.sqrt ε ≤ Real.rpow ε (1 / 8 : ℝ) ∧
      Real.rpow (C₀ * (ε + Real.sqrt ε)) (1 / 4 : ℝ) ≤
        2 * C₀ * Real.rpow ε (1 / 8 : ℝ) := by
  rcases eq_or_lt_of_le hε with h0 | hpos
  · subst h0
    have h8 : Real.rpow (0 : ℝ) (1 / 8 : ℝ) = 0 := Real.zero_rpow (by norm_num)
    have h4 : Real.rpow (C₀ * (0 + Real.sqrt 0)) (1 / 4 : ℝ) = 0 := by
      rw [Real.sqrt_zero, add_zero, mul_zero]
      exact Real.zero_rpow (by norm_num)
    rw [h8, h4, Real.sqrt_zero]
    refine ⟨le_rfl, le_rfl, ?_⟩
    positivity
  · have hsqrt : Real.sqrt ε = Real.rpow ε (1 / 2 : ℝ) := Real.sqrt_eq_rpow ε
    have hε1' : Real.rpow ε 1 = ε := Real.rpow_one ε
    have hmono : ∀ y z : ℝ, z ≤ y → Real.rpow ε y ≤ Real.rpow ε z := fun y z hyz =>
      Real.rpow_le_rpow_of_exponent_ge hpos hε1 hyz
    refine ⟨?_, ?_, ?_⟩
    · exact le_of_eq_of_le hε1'.symm (hmono 1 (1 / 8) (by norm_num))
    · rw [hsqrt]
      exact hmono (1 / 2) (1 / 8) (by norm_num)
    · have hsum : ε + Real.sqrt ε ≤ 2 * Real.sqrt ε := by
        have : ε ≤ Real.sqrt ε := by
          rw [hsqrt]
          exact le_of_eq_of_le hε1'.symm (hmono 1 (1 / 2) (by norm_num))
        linarith
      have hC : 0 ≤ 2 * C₀ := by linarith
      calc Real.rpow (C₀ * (ε + Real.sqrt ε)) (1 / 4 : ℝ)
          ≤ Real.rpow (2 * C₀ * Real.sqrt ε) (1 / 4 : ℝ) := by
            apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
            nlinarith [Real.sqrt_nonneg ε]
        _ = Real.rpow (2 * C₀) (1 / 4 : ℝ) * Real.rpow ε (1 / 8 : ℝ) := by
            change (2 * C₀ * Real.sqrt ε) ^ (1 / 4 : ℝ) =
              (2 * C₀) ^ (1 / 4 : ℝ) * ε ^ (1 / 8 : ℝ)
            rw [Real.mul_rpow hC (Real.sqrt_nonneg ε), Real.sqrt_eq_rpow,
              ← Real.rpow_mul hε]
            norm_num
        _ ≤ 2 * C₀ * Real.rpow ε (1 / 8 : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hε _)
            calc Real.rpow (2 * C₀) (1 / 4 : ℝ) ≤ Real.rpow (2 * C₀) 1 :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
              _ = 2 * C₀ := Real.rpow_one _
