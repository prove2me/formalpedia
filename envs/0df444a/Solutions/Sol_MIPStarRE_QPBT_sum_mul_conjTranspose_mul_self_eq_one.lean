-- Prove2me | solution 1 for MIPStarRE.QPBT.sum_mul_conjTranspose_mul_self_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:55:47.236261+00:00
-- url     : https://prove2.me/submissions/99c5c7a2-b330-46a2-a8ee-f65ca8895f11

-- Generated proof for MIPStarRE.QPBT.sum_mul_conjTranspose_mul_self_eq_one.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
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

theorem solution {α β ι : Type*} [Fintype α]
    [Fintype β] [Fintype ι] [DecidableEq ι]
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (B : _root_.LIDT.MIPStarRE.Quantum.Measurement β ι)
    (hA : _root_.MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : _root_.MIPStarRE.QPBT.Measurement.IsProjective B) :
    ∑ ab : α × β, (A.effect ab.1 * B.effect ab.2)ᴴ * (A.effect ab.1 * B.effect ab.2) =
      1 := by
  have hpt : ∀ (a : α) (b : β),
      (A.effect a * B.effect b)ᴴ * (A.effect a * B.effect b) =
        B.effect b * A.effect a * B.effect b := by
    intro a b
    rw [Matrix.conjTranspose_mul, (hA a).isSelfAdjoint.isHermitian.eq,
      (hB b).isSelfAdjoint.isHermitian.eq, Matrix.mul_assoc _ _ (A.effect a * B.effect b),
      ← Matrix.mul_assoc (A.effect a) (A.effect a), (hA a).isIdempotentElem.eq,
      ← Matrix.mul_assoc]
  rw [Fintype.sum_prod_type_right]
  calc ∑ b : β, ∑ a : α, (A.effect a * B.effect b)ᴴ * (A.effect a * B.effect b)
      = ∑ b : β, B.effect b * (∑ a : α, A.effect a) * B.effect b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => hpt a b
    _ = 1 := by
        simp_rw [A.sum_eq_one, mul_one]
        rw [Finset.sum_congr rfl fun b _ => (hB b).isIdempotentElem.eq]
        exact B.sum_eq_one
