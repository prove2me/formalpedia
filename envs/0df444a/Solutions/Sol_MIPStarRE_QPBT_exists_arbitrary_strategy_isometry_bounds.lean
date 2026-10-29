-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_arbitrary_strategy_isometry_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:54:16.537134+00:00
-- url     : https://prove2.me/submissions/e4f0d99d-63f6-4e21-a520-54a47862e4cf

-- Generated proof for MIPStarRE.QPBT.exists_arbitrary_strategy_isometry_bounds.
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
import Definitions.Def_QPBT_QPBT_ExplicitConstants
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_Unitary
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Definitions.Def_QPBT_QPBT_Test_Soundness_NaimarkReduction
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_isometryTensor_comp
import Theorems.Thm_MIPStarRE_QPBT_deltaQld_mono
import Theorems.Thm_MIPStarRE_QPBT_exists_extraction_witness_of_global_pair_witness_explicit
import Theorems.Thm_MIPStarRE_QPBT_exists_globalPairWitness
import Theorems.Thm_MIPStarRE_QPBT_pauli_naimark_operator_distanceA_le
import Theorems.Thm_MIPStarRE_QPBT_pauli_naimark_operator_distanceB_le
import Theorems.Thm_MIPStarRE_QPBT_pauli_soundness_deltaQld_ofExtractionWitness
import Theorems.Thm_MIPStarRE_QPBT_three_add_six_sq_deltaQld_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
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









/-- A universal constant guarantees an extraction witness at the composed
construction-and-extraction error. -/
theorem exists_extractionWitness_ofGlobalPairWitness :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)
            (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG),
            Nonempty
              (_root_.MIPStarRE.QPBT.ExtractionWitness S w
                (_root_.MIPStarRE.QPBT.deltaExtract C
                  (_root_.MIPStarRE.QPBT.deltaConstructPaulis C epsilon deltaG P.m P.d P.q)
                  P.m P.d P.q)) := by
  refine ⟨_root_.MIPStarRE.QPBT.pauliBaselineExtractionConstant, ?_, ?_⟩
  · unfold _root_.MIPStarRE.QPBT.pauliBaselineExtractionConstant
    norm_num
  · exact _root_.MIPStarRE.QPBT.exists_extraction_witness_of_global_pair_witness_explicit





end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Soundness/NaimarkReduction.lean. -/
/-!
# Naimark reduction for Pauli-test strategies

An arbitrary Pauli-test strategy is dilated questionwise to a projective
strategy on two separately enlarged local spaces. The ground-slice embeddings
are fixed across questions. Compression recovers both original POVM families,
including the complete Pauli-answer postprocessing. Composing any isometry
witness on the dilation with the embeddings returns its state comparison to
the original spaces. Operator-family distance transfer is not asserted here.

## References

Paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`
(`thm:pauli`) and
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190,1862-1876`.
Blueprint `thm:pauli-naimark-reduction-support`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MagicSquareRigidity

noncomputable section











/-- The padded state is precisely the tensor image under the two fixed ground
embeddings; there is no identification of Alice's and Bob's local spaces. -/
theorem pauliNaimarkStrategy_state (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P)) :
    (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).ψ =
      _root_.MIPStarRE.QPBT.isometryTensor (_root_.MIPStarRE.QPBT.pauliNaimarkEmbeddingA P S) (_root_.MIPStarRE.QPBT.pauliNaimarkEmbeddingB P S) S.ψ := by
  change _root_.MIPStarRE.QPBT.padState none none S.ψ = _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState (_root_.MIPStarRE.QPBT.PauliAnswer P) S.ψ
  ext p
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState_apply]
  simp only [_root_.MIPStarRE.QPBT.padState, EuclideanSpace.equiv]
  by_cases hA : p.1.2 = none <;> by_cases hB : p.2.2 = none <;> simp [hA, hB]













/-- The extracted original state is exactly the extracted dilated state. -/
theorem pauli_naimark_witness_state_eq (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P))
    (w : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S)) :
    _root_.MIPStarRE.QPBT.isometryTensor (_root_.MIPStarRE.QPBT.pauliNaimarkWitness P S w).φA
        (_root_.MIPStarRE.QPBT.pauliNaimarkWitness P S w).φB S.ψ =
      _root_.MIPStarRE.QPBT.isometryTensor w.φA w.φB (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).ψ := by
  rw [_root_.MIPStarRE.QPBT.pauliNaimarkStrategy_state]
  exact _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_comp w.φA w.φB
    (_root_.MIPStarRE.QPBT.pauliNaimarkEmbeddingA P S) (_root_.MIPStarRE.QPBT.pauliNaimarkEmbeddingB P S) S.ψ

/-- Consequently the original and dilated witnesses have equal state-distance
quantities from the same ideal auxiliary state. -/
theorem pauli_naimark_witness_state_distance_eq (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P))
    (w : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S)) :
    ‖_root_.MIPStarRE.QPBT.isometryTensor (_root_.MIPStarRE.QPBT.pauliNaimarkWitness P S w).φA
        (_root_.MIPStarRE.QPBT.pauliNaimarkWitness P S w).φB S.ψ -
      _root_.MIPStarRE.QPBT.idealState P (_root_.MIPStarRE.QPBT.pauliNaimarkWitness P S w).aux‖ =
    ‖_root_.MIPStarRE.QPBT.isometryTensor w.φA w.φB (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).ψ -
      _root_.MIPStarRE.QPBT.idealState P w.aux‖ := by
  rw [_root_.MIPStarRE.QPBT.pauli_naimark_witness_state_eq]

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Extraction/SourceUnitary.lean. -/
/-!
# Extraction from a projective Pauli-test strategy

The global polynomial-pair measurements are constructed from the strategy
before applying the extraction theorem for concrete swap unitaries.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1274,1666-1860`.
The numerical corrections are documented in
`docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

noncomputable section



/-- **Source statement:** The projective strategy supplies the global
polynomial-pair measurements internally, and their concrete swap unitaries
extract a normalized auxiliary state and both Pauli measurement families at
the nested construction/extraction scale. No global measurement is assumed.

This is the existence claim of blueprint `lem:qld-unitary`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1685`,
using the global construction at lines 1267-1274. The two-sided unitary
equations and both register placements are recorded in `ExtractionWitness`.
The separate isometry range-projection step of the subsequent soundness proof
at lines 1864-1875 is not asserted here; see
`docs/paper-gaps/qpbt_extraction-transfer.tex`, issue Dengnifer/MIPStarRE-QPBT-bak#123. -/
theorem exists_extractionWitness :
    ∃ a b C : ℝ, 1 < a ∧ 0 < b ∧ b < 1 ∧ 1 ≤ C ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (epsilon : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → ∀ S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon,
          ∃ w : _root_.MIPStarRE.QPBT.GlobalPairWitness S (_root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q),
            Nonempty (_root_.MIPStarRE.QPBT.ExtractionWitness S w
              (_root_.MIPStarRE.QPBT.deltaExtract C
                (_root_.MIPStarRE.QPBT.deltaConstructPaulis C epsilon
                  (_root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q) P.m P.d P.q)
                P.m P.d P.q)) := by
  obtain ⟨a, b, ha, hb, hb1, hglobal⟩ := _root_.MIPStarRE.QPBT.exists_globalPairWitness
  obtain ⟨C, hC, hextract⟩ := _root_.MIPStarRE.QPBT.exists_extractionWitness_ofGlobalPairWitness
  refine ⟨a, b, C, ha, hb, hb1, hC, ?_⟩
  intro P epsilon hepsilon0 hepsilon1 S
  obtain ⟨w⟩ := hglobal P epsilon S
  have hdeltaG : 0 ≤ _root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q := by
    simp only [_root_.MIPStarRE.QPBT.deltaQld, Real.rpow_eq_pow]
    positivity
  exact ⟨w, hextract P epsilon _ hepsilon0 hepsilon1 hdeltaG S w⟩

end



end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Soundness/ProjectiveSetting.lean. -/
/-!
# Pauli isometry bounds for projective settings

The global polynomial-pair measurement and the extraction unitaries are
constructed before transferring the three soundness estimates to local
isometries. The result is restricted to projective settings and errors in
`[0, 1]`; it does not assert soundness for arbitrary strategies.

## References

Blueprint `thm:pauli-projective-setting-isometry-support`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`
and `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
The remaining domain and game-correspondence obligations are recorded in
`docs/paper-gaps/qpbt_extraction-transfer.tex` (issue Dengnifer/MIPStarRE-QPBT-bak#602).
-/

@[expose] public section

namespace MIPStarRE.QPBT

noncomputable section



/-- **Scope restriction:** For projective Pauli-test settings with
`0 ≤ epsilon ≤ 1`, local isometries and a normalized auxiliary state satisfy
the state norm and both complete Pauli-family bounds at a common `deltaQld`
scale. The universal constants are fixed before the setting. The global-pair
and extraction witnesses are constructed internally, not assumed.

This is a formalization-only support result for blueprint `thm:pauli`, not
the unrestricted theorem of the paper at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
The isometry step follows the appendix at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`;
see `docs/paper-gaps/qpbt_extraction-transfer.tex` (issue Dengnifer/MIPStarRE-QPBT-bak#602). -/
theorem exists_projective_setting_isometry_bounds :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (epsilon : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → ∀ S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon,
          ∃ t : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P S.toStrategy,
            ‖_root_.MIPStarRE.QPBT.isometryTensor t.φA t.φB S.toStrategy.ψ - _root_.MIPStarRE.QPBT.idealState P t.aux‖ ≤
              _root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q ∧
            (∀ W : _root_.MIPStarRE.QPBT.PauliKind, _root_.MIPStarRE.QPBT.pauliOperatorDistanceA P S.toStrategy t W ≤
              _root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q) ∧
            (∀ W : _root_.MIPStarRE.QPBT.PauliKind, _root_.MIPStarRE.QPBT.pauliOperatorDistanceB P S.toStrategy t W ≤
              _root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q) := by
  obtain ⟨a, b, C, ha, hb, hb1, hC, hextract⟩ := _root_.MIPStarRE.QPBT.exists_extractionWitness
  obtain ⟨A, B, hA, hB, hB1, htransfer⟩ :=
    _root_.MIPStarRE.QPBT.pauli_soundness_deltaQld_ofExtractionWitness C a b hC ha hb hb1
  refine ⟨A, B, hA, hB, hB1, ?_⟩
  intro P epsilon hepsilon0 hepsilon1 S
  obtain ⟨w, ⟨v⟩⟩ := hextract P epsilon hepsilon0 hepsilon1 S
  exact htransfer P epsilon hepsilon0 hepsilon1 S w v

end

end MIPStarRE.QPBT

/-!
# Pauli isometry bounds for arbitrary strategies

The projective-setting isometry bounds are composed with the questionwise
Naimark dilation.  An arbitrary Pauli-test strategy winning with probability at
least `1 - ε` dilates to a projective setting at the same error, the projective
bounds apply there, and the resulting witness is pulled back to the original
spaces.  The state comparison transfers as an equality; both operator families
transfer with the dilation constants of `pauli_naimark_operator_distanceA_le`,
which the enlarged universal prefactor absorbs.  The error domain is still
restricted to `[0, 1]`.

## References

This is a formalization-only support result for blueprint `thm:pauli`, whose
source statement is at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
The source performs the projective reduction in one sentence at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190`, and the
isometry passage is at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
Blueprint `thm:pauli-arbitrary-strategy-isometry-support`; issue Dengnifer/MIPStarRE-QPBT-bak#614.
-/



open MIPStarRE.QPBT

theorem solution :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
        ∀ S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P S,
            ‖_root_.MIPStarRE.QPBT.isometryTensor w.φA w.φB S.ψ - _root_.MIPStarRE.QPBT.idealState P w.aux‖ ≤
                _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q ∧
            (∀ W : _root_.MIPStarRE.QPBT.PauliKind,
              _root_.MIPStarRE.QPBT.pauliOperatorDistanceA P S w W ≤ _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q) ∧
            (∀ W : _root_.MIPStarRE.QPBT.PauliKind,
              _root_.MIPStarRE.QPBT.pauliOperatorDistanceB P S w W ≤ _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q) := by
  obtain ⟨a, b, ha, hb, hb1, hproj⟩ := _root_.MIPStarRE.QPBT.exists_projective_setting_isometry_bounds
  have haa : a ≤ 21 * a ^ 2 := by nlinarith
  refine ⟨21 * a ^ 2, b, by nlinarith, hb, hb1, ?_⟩
  intro P ε hε0 hε1 S hwin
  have hprojective := hproj P ε hε0 hε1 (_root_.MIPStarRE.QPBT.pauliNaimarkSetting P ε S hwin)
  simp only [_root_.MIPStarRE.QPBT.pauliNaimarkSetting] at hprojective
  obtain ⟨t, hstate, hA, hB⟩ := hprojective
  have hmono : _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q ≤
      _root_.MIPStarRE.QPBT.deltaQld (21 * a ^ 2) b ε P.m P.d P.q :=
    _root_.MIPStarRE.QPBT.deltaQld_mono ha haa le_rfl hb hε0 hε1
  have hstate' : ‖_root_.MIPStarRE.QPBT.isometryTensor t.φA t.φB (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).ψ -
      _root_.MIPStarRE.QPBT.idealState P t.aux‖ ≤ _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q := hstate
  have hsq : ‖_root_.MIPStarRE.QPBT.isometryTensor t.φA t.φB (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).ψ -
      _root_.MIPStarRE.QPBT.idealState P t.aux‖ ^ 2 ≤ _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q ^ 2 := by
    nlinarith [norm_nonneg (_root_.MIPStarRE.QPBT.isometryTensor t.φA t.φB (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).ψ -
      _root_.MIPStarRE.QPBT.idealState P t.aux)]
  have habsorb : 3 * _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q +
      6 * _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q ^ 2 ≤
        _root_.MIPStarRE.QPBT.deltaQld (21 * a ^ 2) b ε P.m P.d P.q :=
    _root_.MIPStarRE.QPBT.three_add_six_sq_deltaQld_le ha hb hε0 hε1
  refine ⟨_root_.MIPStarRE.QPBT.pauliNaimarkWitness P S t, ?_, ?_, ?_⟩
  · rw [_root_.MIPStarRE.QPBT.pauli_naimark_witness_state_distance_eq]
    exact hstate'.trans hmono
  · intro W
    have hA' : _root_.MIPStarRE.QPBT.pauliOperatorDistanceA P (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S) t W ≤
        _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q := hA W
    calc _root_.MIPStarRE.QPBT.pauliOperatorDistanceA P S (_root_.MIPStarRE.QPBT.pauliNaimarkWitness P S t) W
        ≤ 3 * _root_.MIPStarRE.QPBT.pauliOperatorDistanceA P (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S) t W +
            6 * ‖_root_.MIPStarRE.QPBT.isometryTensor t.φA t.φB (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).ψ -
              _root_.MIPStarRE.QPBT.idealState P t.aux‖ ^ 2 :=
          _root_.MIPStarRE.QPBT.pauli_naimark_operator_distanceA_le P S t W
      _ ≤ 3 * _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q +
            6 * _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q ^ 2 := by linarith
      _ ≤ _root_.MIPStarRE.QPBT.deltaQld (21 * a ^ 2) b ε P.m P.d P.q := habsorb
  · intro W
    have hB' : _root_.MIPStarRE.QPBT.pauliOperatorDistanceB P (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S) t W ≤
        _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q := hB W
    calc _root_.MIPStarRE.QPBT.pauliOperatorDistanceB P S (_root_.MIPStarRE.QPBT.pauliNaimarkWitness P S t) W
        ≤ 3 * _root_.MIPStarRE.QPBT.pauliOperatorDistanceB P (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S) t W +
            6 * ‖_root_.MIPStarRE.QPBT.isometryTensor t.φA t.φB (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).ψ -
              _root_.MIPStarRE.QPBT.idealState P t.aux‖ ^ 2 :=
          _root_.MIPStarRE.QPBT.pauli_naimark_operator_distanceB_le P S t W
      _ ≤ 3 * _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q +
            6 * _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q ^ 2 := by linarith
      _ ≤ _root_.MIPStarRE.QPBT.deltaQld (21 * a ^ 2) b ε P.m P.d P.q := habsorb
