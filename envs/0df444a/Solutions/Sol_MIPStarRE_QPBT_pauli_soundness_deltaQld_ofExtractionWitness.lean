-- Prove2me | solution 1 for MIPStarRE.QPBT.pauli_soundness_deltaQld_ofExtractionWitness
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:03:32.578761+00:00
-- url     : https://prove2.me/submissions/a1712e22-3afc-4ada-98eb-0cf3aa6cca69

-- Generated proof for MIPStarRE.QPBT.pauli_soundness_deltaQld_ofExtractionWitness.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Extraction_Unitary
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Definitions.Def_QPBT_QPBT_Test_Soundness_StateTransfer
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtractionWitness_isometryTensor_eq
import Theorems.Thm_MIPStarRE_QPBT_ExtractionWitness_pauli_distance_alice_le
import Theorems.Thm_MIPStarRE_QPBT_ExtractionWitness_pauli_distance_bob_le
import Theorems.Thm_MIPStarRE_QPBT_deltaQld_mono
import Theorems.Thm_MIPStarRE_QPBT_delta_extract_le_delta_qld_explicit
import Theorems.Thm_MIPStarRE_QPBT_sqrt_deltaQld_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Extraction/Unitary.lean. -/
/-!
# Extraction by the swap unitaries

The concrete swap operators below yield the Pauli extraction conclusion. The
local maps are constructed from the global polynomial
measurements, and all operators retain the heterogeneous Alice and Bob
placements. The generalized Pauli projectors use the field and basis fixed by
`P.model`.

## References

The extraction witness records the conclusion of blueprint `lem:qld-unitary`,
from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1860`.
The error-form comparison formalizes `lem:qld-extraction-error-form` and
supports `rem:pauli-robustness-form` in the blueprint; its paper source is
lines 1855-1858 and 1868-1876.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section













/-- Every admissible input coefficient and exponent yield new universal constants
that bound the composed extraction error by an error of `deltaQld` form. -/
theorem deltaExtract_le_deltaQld (C a b : ℝ) (hC : 1 ≤ C) (ha : 1 < a)
    (hb : 0 < b) (hb1 : b < 1) :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' < 1 ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon →
        epsilon ≤ 1 →
        _root_.MIPStarRE.QPBT.deltaExtract C
            (_root_.MIPStarRE.QPBT.deltaConstructPaulis C epsilon
              (_root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q) P.m P.d P.q)
            P.m P.d P.q ≤
          _root_.MIPStarRE.QPBT.deltaQld a' b' epsilon P.m P.d P.q := by
  have hconstant : a ≤ 4 * C ^ 2 * a := by
    have hCsq : 1 ≤ C ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hCsq (by linarith : 0 ≤ a)]
  exact ⟨4 * C ^ 2 * a, b / 8, ha.le.trans hconstant, by positivity, by linarith,
    _root_.MIPStarRE.QPBT.delta_extract_le_delta_qld_explicit C a b hC ha hb hb1⟩

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Soundness/StateTransfer.lean. -/
/-!
# State transfer from supplied extraction data

The extraction witness uses six registers, while the test conclusion groups
each player's first two registers into the auxiliary space. Adjoining the local
EPR states and applying the supplied swap unitaries gives the test isometries.
The squared state error is unchanged by this identification.

## References

Formalization support for blueprint `thm:pauli` and
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`.
This module transports supplied data without invoking either existence theorem.
The companion `OperatorTransfer` module completes both operator comparisons.
The source-facing obligations are tracked by issues #529 and #586 and
`docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MagicSquareRigidity

noncomputable section

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG delta : ℝ}
  {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} {w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG}







open Classical in
/-- The auxiliary-state/EPR vector is unchanged by grouping each player's
first two registers into that player's auxiliary space.
This identity is part of blueprint `thm:pauli-extraction-isometry-construction-support`. -/
theorem ExtractionWitness.idealState_eq (v : _root_.MIPStarRE.QPBT.ExtractionWitness S w delta) :
    _root_.MIPStarRE.QPBT.idealState P v.toPauliSoundnessWitness.aux =
      _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (S.idealExpState v.aux) := by
  ext p
  rfl

open Classical in
/-- The supplied extraction state's squared error is exactly the squared state
error of its test witness. Only the register order changes.
This identity is part of blueprint `thm:pauli-extraction-isometry-construction-support`. -/
theorem ExtractionWitness.state_error_eq (v : _root_.MIPStarRE.QPBT.ExtractionWitness S w delta) :
    ‖_root_.MIPStarRE.QPBT.isometryTensor v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
        S.toStrategy.ψ - _root_.MIPStarRE.QPBT.idealState P v.toPauliSoundnessWitness.aux‖ ^ 2 =
      ‖S.applyBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) S.psiHat -
        S.idealExpState v.aux‖ ^ 2 := by
  rw [v.isometryTensor_eq, v.idealState_eq]
  dsimp +instances only [_root_.MIPStarRE.QPBT.ExtractionWitness.toPauliSoundnessWitness, _root_.MIPStarRE.QPBT.ProjectiveSetting.LocalSpace,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.localSpaceFintype, _root_.MIPStarRE.QPBT.ProjectiveSetting.localSpaceDecidableEq]
  have hsub : ∀ x y : EuclideanSpace ℂ (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB),
      _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) x -
        _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) y =
      _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) (x - y) := by
    intros x y
    rfl
  rw [hsub, _root_.MIPStarRE.QPBT.reindexState_norm_eq]

/-- Conditional transfer of the state estimate from fully supplied extraction
data. The paper-facing theorem must still construct that data; see issue
Dengnifer/MIPStarRE-QPBT-bak#529.
This is blueprint `lem:pauli-extraction-state-distance-support`. -/
theorem ExtractionWitness.state_close_ofExtractionWitness (v : _root_.MIPStarRE.QPBT.ExtractionWitness S w delta) :
    ‖_root_.MIPStarRE.QPBT.isometryTensor v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
        S.toStrategy.ψ - _root_.MIPStarRE.QPBT.idealState P v.toPauliSoundnessWitness.aux‖ ^ 2 ≤ delta := by
  rw [v.state_error_eq]
  exact v.state_close



end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Soundness/OperatorTransfer.lean. -/
/-!
# Operator transfer from supplied extraction data

The complete swap-conjugated measurements intertwine with the local ancilla
isometries. The range-projection estimates then transfer both Pauli families
to the ideal state, with squared error at most four times the extraction error.

## References

Formalization support for the final argument at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`.
This conditional construction uses supplied extraction data in a projective
setting; it does not prove blueprint `thm:pauli`. The omitted range projection
is documented in `docs/paper-gaps/qpbt_extraction-transfer.tex` (issue
Dengnifer/MIPStarRE-QPBT-bak#529).
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MagicSquareRigidity DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement

noncomputable section

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG delta : ℝ}
  {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} {w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG}

























/-- Isometry transfer bounds for supplied extraction data in a projective
setting. The common bound is `max (sqrt delta) (4 * delta)`: the state norm
is unsquared and both operator distances sum squared norms over all outcomes.
This is blueprint `thm:pauli-concrete-isometry-transfer-support`, a
conditional support theorem for `thm:pauli`, not the source theorem.
The separate component bounds are blueprint
`lem:pauli-extraction-state-distance-support`,
`thm:pauli-extraction-alice-distance-support`, and
`thm:pauli-extraction-bob-distance-support`.
Discharging the supplied-data premise requires the global-pair construction
and extraction; see `docs/paper-gaps/qpbt_extraction-transfer.tex`, issue
Dengnifer/MIPStarRE-QPBT-bak#529. -/
theorem ExtractionWitness.isometry_transfer_bounds (v : _root_.MIPStarRE.QPBT.ExtractionWitness S w delta) :
    ∃ t : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P S.toStrategy,
      ‖_root_.MIPStarRE.QPBT.isometryTensor t.φA t.φB S.toStrategy.ψ - _root_.MIPStarRE.QPBT.idealState P t.aux‖ ≤
        max (Real.sqrt delta) (4 * delta) ∧
      (∀ W : _root_.MIPStarRE.QPBT.PauliKind, _root_.MIPStarRE.QPBT.pauliOperatorDistanceA P S.toStrategy t W ≤
        max (Real.sqrt delta) (4 * delta)) ∧
      (∀ W : _root_.MIPStarRE.QPBT.PauliKind, _root_.MIPStarRE.QPBT.pauliOperatorDistanceB P S.toStrategy t W ≤
        max (Real.sqrt delta) (4 * delta)) := by
  refine ⟨v.toPauliSoundnessWitness, ?_, ?_, ?_⟩
  · exact (Real.le_sqrt_of_sq_le v.state_close_ofExtractionWitness).trans (le_max_left _ _)
  · intro W
    exact (v.pauli_distance_alice_le W).trans (le_max_right _ _)
  · intro W
    exact (v.pauli_distance_bob_le W).trans (le_max_right _ _)



private theorem four_mul_deltaQld_le {a b epsilon : ℝ}
    (ha : 1 ≤ a) (hepsilon : 0 ≤ epsilon) :
    4 * _root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q ≤ _root_.MIPStarRE.QPBT.deltaQld (4 * a) b epsilon P.m P.d P.q := by
  have hmd : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hpow := Real.rpow_le_rpow_of_exponent_le hmd (show a ≤ 4 * a by linarith)
  unfold _root_.MIPStarRE.QPBT.deltaQld
  calc
    4 * (a * Real.rpow ((P.m * P.d : ℕ) : ℝ) a *
        (Real.rpow epsilon b + Real.rpow (P.q : ℝ) (-b) +
          Real.rpow 2 (-(b * ((P.m * P.d : ℕ) : ℝ))))) =
      (4 * a) * Real.rpow ((P.m * P.d : ℕ) : ℝ) a *
        (Real.rpow epsilon b + Real.rpow (P.q : ℝ) (-b) +
          Real.rpow 2 (-(b * ((P.m * P.d : ℕ) : ℝ)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by linarith))
      (add_nonneg (add_nonneg (Real.rpow_nonneg hepsilon _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (by norm_num) _))





end

end MIPStarRE.QPBT

/-!
# Operator transfer from supplied extraction data

The complete swap-conjugated measurements intertwine with the local ancilla
isometries. The range-projection estimates then transfer both Pauli families
to the ideal state, with squared error at most four times the extraction error.

## References

Formalization support for the final argument at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`.
This conditional construction uses supplied extraction data in a projective
setting; it does not prove blueprint `thm:pauli`. The omitted range projection
is documented in `docs/paper-gaps/qpbt_extraction-transfer.tex` (issue
Dengnifer/MIPStarRE-QPBT-bak#529).
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.MagicSquareRigidity MIPStarRE.QPBT.DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement



variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG delta : ℝ}
  {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} {w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG}

theorem solution
    (C a b : ℝ) (hC : 1 ≤ C) (ha : 1 < a) (hb : 0 < b) (hb1 : b < 1) :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' < 1 ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon → epsilon ≤ 1 →
        ∀ (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)
          (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S (_root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q))
          (_v : _root_.MIPStarRE.QPBT.ExtractionWitness S w
            (_root_.MIPStarRE.QPBT.deltaExtract C (_root_.MIPStarRE.QPBT.deltaConstructPaulis C epsilon
              (_root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q) P.m P.d P.q) P.m P.d P.q)),
          ∃ t : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P S.toStrategy,
            ‖_root_.MIPStarRE.QPBT.isometryTensor t.φA t.φB S.toStrategy.ψ - _root_.MIPStarRE.QPBT.idealState P t.aux‖ ≤
              _root_.MIPStarRE.QPBT.deltaQld a' b' epsilon P.m P.d P.q ∧
            (∀ W : _root_.MIPStarRE.QPBT.PauliKind, _root_.MIPStarRE.QPBT.pauliOperatorDistanceA P S.toStrategy t W ≤
              _root_.MIPStarRE.QPBT.deltaQld a' b' epsilon P.m P.d P.q) ∧
            (∀ W : _root_.MIPStarRE.QPBT.PauliKind, _root_.MIPStarRE.QPBT.pauliOperatorDistanceB P S.toStrategy t W ≤
              _root_.MIPStarRE.QPBT.deltaQld a' b' epsilon P.m P.d P.q) := by
  obtain ⟨A, B, hA, hB, hB1, herror⟩ := _root_.MIPStarRE.QPBT.deltaExtract_le_deltaQld C a b hC ha hb hb1
  refine ⟨4 * A, B / 2, by linarith, by positivity, by linarith, ?_⟩
  intro P epsilon hepsilon hepsilon1 S w v
  obtain ⟨t, ht, htA, htB⟩ := v.isometry_transfer_bounds
  have hmono := _root_.MIPStarRE.QPBT.deltaQld_mono (P := P) hA (le_refl A) (show B / 2 ≤ B by linarith)
    (show 0 < B / 2 by positivity) hepsilon hepsilon1
  have hfour := four_mul_deltaQld_le (P := P) (b := B / 2) hA hepsilon
  have hnonneg : 0 ≤ _root_.MIPStarRE.QPBT.deltaQld A (B / 2) epsilon P.m P.d P.q := by
    have hA0 := zero_le_one.trans hA
    simp only [_root_.MIPStarRE.QPBT.deltaQld, Real.rpow_eq_pow]
    positivity
  have hcommon : max (Real.sqrt _) (4 * _) ≤
      _root_.MIPStarRE.QPBT.deltaQld (4 * A) (B / 2) epsilon P.m P.d P.q := max_le
    (((Real.sqrt_le_sqrt (herror P epsilon hepsilon hepsilon1)).trans
      (_root_.MIPStarRE.QPBT.sqrt_deltaQld_le hA hepsilon)).trans
        ((show _root_.MIPStarRE.QPBT.deltaQld A (B / 2) epsilon P.m P.d P.q ≤
          4 * _root_.MIPStarRE.QPBT.deltaQld A (B / 2) epsilon P.m P.d P.q by linarith).trans hfour))
    ((mul_le_mul_of_nonneg_left
      ((herror P epsilon hepsilon hepsilon1).trans hmono)
      (by norm_num : (0 : ℝ) ≤ 4)).trans hfour)
  exact ⟨t, ht.trans hcommon, fun W => (htA W).trans hcommon,
    fun W => (htB W).trans hcommon⟩
