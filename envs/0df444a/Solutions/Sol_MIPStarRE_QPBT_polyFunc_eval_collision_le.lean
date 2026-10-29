-- Prove2me | solution 1 for MIPStarRE.QPBT.polyFunc_eval_collision_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:24:57.15915+00:00
-- url     : https://prove2.me/submissions/9dabc113-cc60-4a3a-81b7-51cef504a835

-- Generated proof for MIPStarRE.QPBT.polyFunc_eval_collision_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Distribution.IsProbability
end LIDT.MIPStarRE.LDT.Distribution.IsProbability
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum.Measurement
end LIDT.MIPStarRE.Quantum.Measurement
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Upstream.lean. -/
/-!
# Public helpers for the upstream LIDT interface

These finite-sum and measurement lemmas support the QPBT without modifying its LIDT dependency.
The marginal-state construction and rank-zero argument adapt the private proofs in
`LionSR/MIPStarRE`, commit `f382c801026f53a9efc260fdee707cb35e0adb15`, module
`MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair`.
The remaining lemmas are QPBT extensions of the upstream measurement and distribution APIs.
Their proofs use the public definitions and Mathlib finite-dimensional linear algebra.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder



namespace LIDT
namespace MIPStarRE.LDT



/-- A uniform average over a finite type is its normalized finite sum. -/
theorem avgOver_uniform_eq_inv_card_mul_sum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) f = (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  unfold _root_.LIDT.MIPStarRE.LDT.avgOver _root_.LIDT.MIPStarRE.LDT.uniformDistribution _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset
  simp only [Finset.mem_univ, ite_true, Finset.card_univ, one_div, Finset.mul_sum]


end MIPStarRE.LDT
end LIDT

/-!
# Real polynomial collision bounds

The existing Schwartz–Zippel estimate for bounded polynomial representatives
is expressed as a nonnegative rational cardinality ratio. This module converts
it to the real uniform average used by the sandwich support comparison and
specializes it to the polynomial outcomes of the Pauli basis test.

## References

* `references/qpbt-paper/04_preliminaries.tex`, `lem:schwartz-zippel`.
* Blueprint `lem:schwartz-zippel-individual` and the collision calculation
  preceding `eq:qld-nonencoding-mass` in `sec:separating`.
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1483-1492`,
  the consistency calculation in `lem:qld-construct-the-paulis` whose decoder
  substitution requires the blueprint's nonencoding-mass estimate.
* `docs/paper-gaps/qpbt_decoding-identity.tex`, for that substitution's scope.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.LDT.Preliminaries

theorem solution {m d : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (first second : _root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc m K d) (hne : first ≠ second) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin m → K))
      (fun point => if MvPolynomial.eval point first.1 = MvPolynomial.eval point second.1
        then (1 : ℝ) else 0) ≤ (m * d : ℝ) / Fintype.card K := by
  have havg :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin m → K))
        (fun point => if MvPolynomial.eval point first.1 = MvPolynomial.eval point second.1
          then (1 : ℝ) else 0) =
        (_root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability m K first.1 second.1 : ℝ) := by
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_eq_inv_card_mul_sum, ← Finset.sum_filter]
    simp [_root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability, div_eq_mul_inv, mul_comm]
  rw [havg]
  have hbound := _root_.LIDT.MIPStarRE.LDT.Preliminaries.schwartzZippel_individualDegree first second hne
  have hreal : (_root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability m K first.1 second.1 : ℝ) ≤
      ((((m * d : ℕ) : ℚ≥0) / Fintype.card K) : ℝ) := by
    exact_mod_cast hbound
  simpa using hreal
