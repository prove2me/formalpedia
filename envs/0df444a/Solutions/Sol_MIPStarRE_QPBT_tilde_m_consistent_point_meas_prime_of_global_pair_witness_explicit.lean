-- Prove2me | solution 1 for MIPStarRE.QPBT.tilde_m_consistent_point_meas_prime_of_global_pair_witness_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:05:34.74169+00:00
-- url     : https://prove2.me/submissions/679e5367-5ec2-4423-b48a-b539e4b85d29

-- Generated proof for MIPStarRE.QPBT.tilde_m_consistent_point_meas'_of_global_pair_witness_explicit.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_Decoding
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_Consistency
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_EncodingSupport
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_SandwichProduct_consistencyDefect_placed_eq_avg_point
import Theorems.Thm_MIPStarRE_QPBT_SandwichProduct_point_codeword_defect_le_avg_evaluated_add
import Theorems.Thm_MIPStarRE_QPBT_global_marginal_encoding_consistency_explicit
import Theorems.Thm_MIPStarRE_QPBT_mass_outside_support_le_point_defect
import Theorems.Thm_MIPStarRE_QPBT_polyFunc_eval_collision_le
import Theorems.Thm_MIPStarRE_QPBT_stateQForm_placeSide_alice_tensor_one
import Theorems.Thm_MIPStarRE_QPBT_tildeM_consistencyDefect_le_deltaG_add_nonencoding_prime

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Extraction/EncodingSupport.lean. -/
/-! # Encoding-supported Pauli reference measurements

The reference measurement measures the strategy's Pauli answer and an independent
ideal Pauli answer, then returns the bounded encoding of their sum. Its effects
vanish outside the encoding image. Evaluation of its polynomial outcome is the
convolution of the evaluated strategy measurement and the ideal point projectors.

These are internal auxiliary constructions for blueprint `eq:qld-nonencoding-mass`
and `lem:qld-nonencoding-mass-bound`, not the quantitative support estimate. No
winning premise or global polynomial-pair witness is used or constructed here.

## References

The encoding is paper `eq:low-degree-encoding-definition` in
`references/qpbt-paper/04_preliminaries.tex:882-897`. The convolution is the Pauli
answer replacement of the expanded point measurement at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:383-418`.
The corrected use in `lem:qld-construct-the-paulis` is recorded in blueprint
`eq:qld-nonencoding-mass` and `docs/paper-gaps/qpbt_decoding-identity.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum

variable {params : _root_.MIPStarRE.QPBT.AdmissibleParams} {error : ℝ}





namespace ProjectiveSetting



/-- The reference effect sums the product effects over pairs whose sum encodes
the specified polynomial representative. -/
theorem encodingPauliMeas_effect (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (basis : _root_.MIPStarRE.QPBT.PauliKind) (poly : _root_.MIPStarRE.QPBT.Poly params) :
    (setting.encodingPauliMeas side basis).effect poly =
      ∑ answers ∈ Finset.univ.filter
          (fun answers : _root_.MIPStarRE.QPBT.PauliRegister params × _root_.MIPStarRE.QPBT.PauliRegister params =>
            _root_.MIPStarRE.QPBT.encodingPoly (answers.1 + answers.2) = poly),
        _root_.MIPStarRE.QPBT.heteroKron ((setting.pauliMeas side basis).effect answers.1)
          (_root_.MIPStarRE.QPBT.pauliProj basis answers.2) :=
  rfl





/-- A nonencoding polynomial has zero reference effect. This is exact support of
the auxiliary measurement, not a bound on the global polynomial measurement. -/
theorem encodingPauliMeas_effect_eq_zero_of_not_isEncoding
    (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error) (side : _root_.MIPStarRE.QPBT.PlayerSide) (basis : _root_.MIPStarRE.QPBT.PauliKind)
    (poly : _root_.MIPStarRE.QPBT.Poly params) (hpoly : ¬ _root_.MIPStarRE.QPBT.IsEncoding poly) :
    (setting.encodingPauliMeas side basis).effect poly = 0 := by
  classical
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.encodingPauliMeas_effect]
  apply Finset.sum_eq_zero
  intro answers hanswers
  exact False.elim (hpoly ((Finset.mem_filter.mp hanswers).2 ▸
    _root_.MIPStarRE.QPBT.isEncoding_encodingPoly (answers.1 + answers.2)))





end ProjectiveSetting

end MIPStarRE.QPBT

/- Source helpers from QPBT/Extraction/PolynomialCollision.lean. -/
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

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.LDT.Preliminaries



/-- The collision hypothesis for the sandwich support comparison on QPBT
polynomial outcomes, with the field cardinality written as `P.q`.

This specializes `polyFunc_eval_collision_le` to the fixed field model and
`evalPoly`; it adds no assumptions to the admissible parameter domain of
blueprint `eq:qld-nonencoding-mass`. -/
theorem poly_eval_collision_le {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (first second : _root_.MIPStarRE.QPBT.Poly P) (hne : first ≠ second) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
      (fun point => if _root_.MIPStarRE.QPBT.evalPoly first point = _root_.MIPStarRE.QPBT.evalPoly second point then (1 : ℝ) else 0) ≤
        (P.m * P.d : ℝ) / P.q := by
  have hcard : Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) = P.q :=
    @_root_.LIDT.MIPStarRE.LDT.FieldModel.card P.q P.model.toFieldModel
  unfold _root_.MIPStarRE.QPBT.evalPoly
  conv_rhs => rw [← hcard]
  exact _root_.MIPStarRE.QPBT.polyFunc_eval_collision_le first second hne

end MIPStarRE.QPBT

/- Source helpers from QPBT/Extraction/NonencodingSupport.lean. -/
/-!
# Consistency with encoding-supported reference measurements

The Pauli-basis check remains a consistency estimate after adjoining the
perfectly correlated ideal point measurement. Schwartz-Zippel then controls
mass outside the encoding image by evaluated reference inconsistency.

## References

- Blueprint `eq:qld-nonencoding-mass` and `lem:qld-nonencoding-mass-bound`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:197-264,383-418`.
- `docs/paper-gaps/qpbt_decoding-identity.tex`.
- The reference measurements and comparison estimates express the convolution
  with the ideal Pauli point projectors.
- These are auxiliary estimates for a supplied witness, not its construction.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open scoped Classical

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus ProjectiveSetting

noncomputable section



/-- A polynomial measurement's mass outside the encoding image is at most
its evaluated inconsistency with an encoding-supported reference, plus `md/q`.
This is the Schwartz-Zippel step in blueprint `eq:qld-nonencoding-mass`.
The reference support is explicit because this auxiliary applies to any POVM;
the concrete reference above proves it without an additional strategy premise. -/
theorem mass_outside_encoding_le_evaluated_defect {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (meas : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.Poly P) I) (reference : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.Poly P) J)
    (psi : EuclideanSpace ℂ (I × J)) (hpsi : ‖psi‖ = 1)
    (hsupport : ∀ g, ¬ _root_.MIPStarRE.QPBT.IsEncoding g → reference.effect g = 0) :
    (∑ g ∈ Finset.univ.filter (fun g : _root_.MIPStarRE.QPBT.Poly P => ¬ _root_.MIPStarRE.QPBT.IsEncoding g),
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm psi (_root_.MIPStarRE.QPBT.heteroKron (meas.effect g) 1)) ≤
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron ((meas.postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 ((reference.postprocess
          (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a)) psi + (P.m * P.d : ℝ) / P.q := by
  classical
  have hmass := _root_.MIPStarRE.QPBT.mass_outside_support_le_point_defect meas reference psi
    (Finset.univ.filter _root_.MIPStarRE.QPBT.IsEncoding) (by simpa using hsupport)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmass
  have hcollision := _root_.MIPStarRE.QPBT.SandwichProduct.point_codeword_defect_le_avg_evaluated_add
    meas reference psi _root_.MIPStarRE.QPBT.evalPoly ((P.m * P.d : ℝ) / P.q) hpsi
    (by positivity) _root_.MIPStarRE.QPBT.poly_eval_collision_le
  refine hmass.trans (hcollision.trans_eq ?_)
  rw [_root_.MIPStarRE.QPBT.SandwichProduct.consistencyDefect_placed_eq_avg_point]













end

end MIPStarRE.QPBT

/-!
# Supplied-witness point consistency for extraction

The two point estimates combine the point-consistency relations of a supplied
global polynomial-pair measurement with encoding support and polynomial
collision bounds.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1463-1492`.
* `docs/paper-gaps/qpbt_decoding-identity.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)
            (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) (W : _root_.MIPStarRE.QPBT.PauliKind),
            _root_.MIPStarRE.QPBT.consistencyDefect
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
              (fun u a => S.placeSide .alice
                (_root_.MIPStarRE.QPBT.tildeM w .alice W (_root_.MIPStarRE.QPBT.indicatorVec u) a))
              (fun u a =>
                S.placePlayer .bob ((S.pointMeas .bob W u).effect a))
              S.psiHat ≤
                _root_.MIPStarRE.QPBT.deltaConstructPaulis (2 + 2 * Real.sqrt 172)
                  epsilon deltaG P.m P.d P.q := by
  classical
  intro P epsilon deltaG hepsilon _ hdeltaG S w W
  have hdefect := _root_.MIPStarRE.QPBT.tildeM_consistencyDefect_le_deltaG_add_nonencoding_prime w W
  have href :=
    (_root_.MIPStarRE.QPBT.global_marginal_encoding_consistency_explicit P epsilon deltaG hepsilon S w W).1
  have hmass := _root_.MIPStarRE.QPBT.mass_outside_encoding_le_evaluated_defect
    (w.marginalPoly .alice W) (S.encodingPauliMeas .bob W)
    (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState_norm S)
    (S.encodingPauliMeas_effect_eq_zero_of_not_isEncoding .bob W)
  have hm : _root_.MIPStarRE.QPBT.nonencodingMarginalMass w .alice W ≤
      deltaG + (1 + 2 * Real.sqrt 172) * Real.sqrt epsilon +
        (P.m * P.d : ℝ) / P.q := by
    unfold _root_.MIPStarRE.QPBT.nonencodingMarginalMass
    change (∑ g ∈ Finset.univ.filter (fun g : _root_.MIPStarRE.QPBT.Poly P => ¬ _root_.MIPStarRE.QPBT.IsEncoding g),
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat (S.placeSide .alice
        (_root_.MIPStarRE.QPBT.heteroKron ((w.marginalPoly .alice W).effect g) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))))) ≤ _
    simp_rw [_root_.MIPStarRE.QPBT.stateQForm_placeSide_alice_tensor_one S _
      (Matrix.nonneg_iff_posSemidef.mp ((w.marginalPoly .alice W).pos _)).isHermitian]
    exact hmass.trans (add_le_add href le_rfl)
  unfold _root_.MIPStarRE.QPBT.deltaConstructPaulis
  rw [Nat.cast_mul]
  have hratio : 0 ≤ (P.m * P.d : ℝ) / P.q := by positivity
  have hsqrt : 0 ≤ Real.sqrt epsilon := Real.sqrt_nonneg epsilon
  have hroot : 0 ≤ Real.sqrt (172 : ℝ) := Real.sqrt_nonneg _
  nlinarith
