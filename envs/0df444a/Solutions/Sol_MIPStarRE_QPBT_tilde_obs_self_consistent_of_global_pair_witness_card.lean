-- Prove2me | solution 1 for MIPStarRE.QPBT.tilde_obs_self_consistent_of_global_pair_witness_card
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:27:10.242576+00:00
-- url     : https://prove2.me/submissions/a323eb54-58a3-4130-98de-a63308bf3830

-- Generated proof for MIPStarRE.QPBT.tilde_obs_self_consistent_of_global_pair_witness_card.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_Decoding
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Extraction_PullingMeasurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_pullingMeas_eval_consistencyDefect_le
import Theorems.Thm_MIPStarRE_QPBT_tildeM_consistencyDefect_le_pulling_eval_add
import Theorems.Thm_MIPStarRE_QPBT_tildeObs_opDistSq_le_four_consistencyDefect

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Extraction/PullingMeasurement.lean. -/
/-!
# Polynomial outcomes in the pulling argument

The joint measurement of a polynomial marginal and an ideal Pauli register
returns the difference between the polynomial and the encoding of the register.
Decoding this difference gives exactly the pulled-apart measurement. Polynomial
collision estimates apply to these representatives without an encoding-support
restriction on the original marginal.

## References

- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1530-1605`,
  `eq:qld-pulling-11`, `eq:qld-pulling-12`, and the following symmetry argument.
- `docs/paper-gaps/qpbt_decoding-identity.tex`; only decoder linearity and its
  left-inverse identity are used here.
- Issue Dengnifer/MIPStarRE-QPBT-bak#123 tracks the `eq:qld-pulling-cons` extraction obligation;
  these
  auxiliary results do not assert it. This module was originally filed
  under issue Dengnifer/MIPStarRE-QPBT-bak#520, now closed.
- The collision estimate compares unequal difference polynomials under uniform
  evaluation.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus
open WinImplications

noncomputable section

open scoped Classical



















/-- Observable consistency reduces to the evaluated difference-polynomial
defect. The coefficient four, uniform register average, and fixed basis
coordinate are exactly those of the established character conversion.
This estimate assumes no bound on the remaining evaluated defect. -/
theorem tildeObs_opDistSq_le_pulling_eval_add {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {epsilon deltaG : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
    (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) (W : _root_.MIPStarRE.QPBT.PauliKind) (j : Fin P.model.basisDim) :
    _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P))
        (fun u => S.placeSide .alice (_root_.MIPStarRE.QPBT.tildeObs w .alice W u j))
        (fun u => S.placeSide .bob (_root_.MIPStarRE.QPBT.tildeObs w .bob W u j)) S.psiHat ≤
      4 * (_root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => S.placeSide .alice
          (((_root_.MIPStarRE.QPBT.pullingMeas w .alice W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a))
        (fun u a => S.placeSide .bob
          (((_root_.MIPStarRE.QPBT.pullingMeas w .bob W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a))
        S.psiHat + (P.m * P.d : ℝ) / P.q) := by
  exact (_root_.MIPStarRE.QPBT.tildeObs_opDistSq_le_four_consistencyDefect w W j).trans
    (mul_le_mul_of_nonneg_left (_root_.MIPStarRE.QPBT.tildeM_consistencyDefect_le_pulling_eval_add w W)
      (by norm_num))

end

end MIPStarRE.QPBT

/-!
# Self-consistency of the pulled-apart observables

The difference-polynomial measurements reduce observable self-consistency to
point self-consistency and polynomial collision. The global witness remains
an explicit premise.

## References

- Blueprint `lem:qld-construct-the-paulis-given-global-pair`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1476-1662`.
- `docs/paper-gaps/qpbt_extraction-transfer.tex`, issue Dengnifer/MIPStarRE-QPBT-bak#123.
- The joint source obligation for `lem:qld-construct-the-paulis` is stated in
  `Extraction.Construction`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)
            (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) (W : _root_.MIPStarRE.QPBT.PauliKind)
            (j : Fin P.model.basisDim),
            _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P))
              (fun u => S.placeSide .alice (_root_.MIPStarRE.QPBT.tildeObs w .alice W u j))
              (fun u => S.placeSide .bob (_root_.MIPStarRE.QPBT.tildeObs w .bob W u j))
              S.psiHat ≤
                _root_.MIPStarRE.QPBT.deltaConstructPaulis
                  (48 + 32 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ))
                  epsilon deltaG P.m P.d P.q := by
  have hcard : 0 ≤ (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) := Nat.cast_nonneg _
  intro P epsilon deltaG hepsilon hepsilon_one hdeltaG S w W j
  have hbound := (_root_.MIPStarRE.QPBT.tildeObs_opDistSq_le_pulling_eval_add w W j).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (_root_.MIPStarRE.QPBT.pullingMeas_eval_consistencyDefect_le w W) (le_refl _))
      (by norm_num : (0 : ℝ) ≤ 4))
  have heps : epsilon ≤ Real.sqrt epsilon := Real.le_sqrt_self_iff.mpr hepsilon_one
  have hsqrt := Real.sqrt_nonneg epsilon
  have hratio : 0 ≤ (P.m * P.d : ℝ) / P.q :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left heps
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) hcard)
  refine hbound.trans ?_
  unfold _root_.MIPStarRE.QPBT.deltaConstructPaulis
  rw [Nat.cast_mul]
  nlinarith [mul_nonneg hcard hdeltaG, mul_nonneg hcard hratio]
