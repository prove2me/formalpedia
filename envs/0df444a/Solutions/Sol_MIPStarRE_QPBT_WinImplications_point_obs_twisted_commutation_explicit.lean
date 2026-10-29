-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.point_obs_twisted_commutation_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:05:34.904274+00:00
-- url     : https://prove2.me/submissions/43180fac-f1a5-41bd-9256-32ad7d256658

-- Generated proof for MIPStarRE.QPBT.WinImplications.point_obs_twisted_commutation_explicit.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_TwistedCommutation
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_point_obs_anticommutator_anticomm_le_explicit
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_point_obs_commutator_comm_le_alice_explicit
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_twisted_commutation_of_halves

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Observables/Defs.lean. -/
/-!
# Typed strategy measurements and point observables

This file fixes a projective, possibly heterogeneous strategy for the Pauli
basis test and extracts the typed measurement families used in the analysis.
Malformed answers are folded into a fixed valid answer, so the extracted
families remain complete measurements. The winning hypothesis bounds their
original wrong-form mass by the rejection probability. `Option` is used only
for the completed line-evaluation classes.

## References

The ambient strategy convention and the observable `W^r(u)` are in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190`,
corresponding to blueprint `def:strategy-observables`. The typed question
and answer forms come from blueprint `def:pauli-question-distribution` and
`def:pauli-win-predicate`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1225`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section







namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}





























-- The support rewrites below elaborate the `Fintype` instance of
-- `PauliEdge × PauliSpace P`, whose nested sigma/sum instance chain exceeds the
-- default recursion depth.
































































/-- The zero-label point observable is the identity by measurement completeness. -/
theorem pointObs_zero (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    S.pointObs side W 0 u = 1 := by
  classical
  simpa [_root_.MIPStarRE.QPBT.ProjectiveSetting.pointObs, _root_.MIPStarRE.QPBT.fixedBinTrace, _root_.MIPStarRE.QPBT.phaseSign] using (S.pointMeas side W u).sum_eq_one

/-- The point observable squares to the identity. This is the assertion that
the operator in `def:strategy-observables` has eigenvalues in `{+1,-1}`;
paper `14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`def:strategy-observables`. -/
theorem pointObs_sq_eq_one (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (r : _root_.MIPStarRE.QPBT.PauliScalar P) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    S.pointObs side W r u * S.pointObs side W r u = 1 := by
  haveI : CharP (_root_.MIPStarRE.QPBT.PauliScalar P) 2 :=
    (Algebra.charP_iff (ZMod 2) (_root_.MIPStarRE.QPBT.PauliScalar P) 2).mp (ZMod.charP 2)
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.pointObs_mul, CharTwo.add_self_eq_zero, _root_.MIPStarRE.QPBT.ProjectiveSetting.pointObs_zero]

/-- The point observable is Hermitian. This is the self-adjoint part of the
observable assertion following `eq:qld-strat-obs`, paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`def:strategy-observables`. -/
theorem pointObs_isHermitian (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (r : _root_.MIPStarRE.QPBT.PauliScalar P) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointObs side W r u).IsHermitian := by
  classical
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.pointObs, Matrix.IsHermitian]
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Matrix.conjTranspose_smul, _root_.MIPStarRE.QPBT.star_phaseSign]
  rw [(Matrix.nonneg_iff_posSemidef.mp
    ((S.pointMeas side W u).pos a)).isHermitian.eq]

end ProjectiveSetting

end

end MIPStarRE.QPBT

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





/-- The strategy point observable is a reflection. Paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`ch14_qpbt_observables.tex:573-610`. -/
theorem pointObs_conjTranspose_mul_self {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (r : _root_.MIPStarRE.QPBT.PauliScalar P) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointObs side W r u)ᴴ * S.pointObs side W r u = 1 := by
  rw [(S.pointObs_isHermitian side W r u).eq]
  exact S.pointObs_sq_eq_one side W r u



/-! ## The anticommuting half of the twisted commutation -/





















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



/-! ## The commuting half on Alice's factor -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyTwisted

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε),
      0 ≤ ε →
      _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P))
        (fun ω => _root_.MIPStarRE.QPBT.heteroKron
          (S.pointObs .alice .X ω.2.2.1 ω.1 *
            S.pointObs .alice .Z ω.2.2.2 ω.2.1) 1)
        (fun ω => _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          _root_.MIPStarRE.QPBT.heteroKron
            (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
              S.pointObs .alice .X ω.2.2.1 ω.1) 1)
        S.toStrategy.ψ ≤
          (2 * (1024 * (2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) +
              1024 * Real.sqrt (4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ))) +
            (96 * (16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) +
              3551040 * (16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ))) + 4) *
            Real.sqrt ε := by
  classical
  intro P ε S hε
  exact _root_.MIPStarRE.QPBT.WinImplications.twisted_commutation_of_halves
    (fun ω => S.pointObs .alice .X ω.2.2.1 ω.1)
    (fun ω => S.pointObs .alice .Z ω.2.2.2 ω.2.1)
    S.toStrategy.ψ S.toStrategy.ψ_norm
    (fun ω => _root_.MIPStarRE.QPBT.WinImplications.pointObs_conjTranspose_mul_self S .alice .X ω.2.2.1 ω.1)
    (fun ω => _root_.MIPStarRE.QPBT.WinImplications.pointObs_conjTranspose_mul_self S .alice .Z ω.2.2.2 ω.2.1)
    hε (by positivity) (by positivity)
    (_root_.MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_alice_explicit P ε S hε)
    (_root_.MIPStarRE.QPBT.WinImplications.point_obs_anticommutator_anticomm_le_explicit P ε S hε)
