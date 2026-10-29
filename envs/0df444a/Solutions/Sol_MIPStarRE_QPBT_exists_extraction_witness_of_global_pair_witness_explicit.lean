-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_extraction_witness_of_global_pair_witness_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:17:59.016906+00:00
-- url     : https://prove2.me/submissions/19b9ceb5-0725-4f23-9681-53c190e7543b

-- Generated proof for MIPStarRE.QPBT.exists_extraction_witness_of_global_pair_witness_explicit.
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
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_ExplicitConstants
import Definitions.Def_QPBT_QPBT_Extraction_ConcretePauliComparison
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Extraction_Unitary
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_extraction_pauli_dist_le
import Theorems.Thm_MIPStarRE_QPBT_evaluated_pauli_tilde_consistency_of_global_pair_witness_explicit
import Theorems.Thm_MIPStarRE_QPBT_exists_extractionWitness_ofGlobalPairWitness_of_four_le
import Theorems.Thm_MIPStarRE_QPBT_exists_extraction_aux_of_global_pair_witness_explicit
import Theorems.Thm_MIPStarRE_QPBT_extraction_small_error_absorption

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.GlobalPairWitness
end MIPStarRE.QPBT.GlobalPairWitness
namespace MIPStarRE.QPBT.PauliKind
end MIPStarRE.QPBT.PauliKind

/- Source helpers from QPBT/Extraction/Observables.lean. -/
/-!
# Pulled-apart Pauli observables

This module constructs the measurements and observables used to pull the two
Pauli bases onto separate registers. The construction retains the distinct
local spaces of the two players and uses the binary basis fixed in the
canonical field model.

## References

The product form and observable relations formalize blueprint
`lem:tildew-product-form`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1415-1456`.
The swap identities formalize blueprint `lem:v-swap-conjugation`, from paper
lines 1687-1713.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.LDT.Preliminaries LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Pulled-apart measurements and observables -/

























/-! ## Swap conjugation -/















/-- The swap map is a left unitary. This is the reverse exact unitarity
calculation implicit in blueprint
`lem:v-swap-conjugation`, paper
`14_analysis_of_the_pauli_basis_test.tex:1687-1699`.

For finite square matrices, the right inverse identity also gives the left
inverse identity. -/
theorem conjTranspose_mul_swapUnitary {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {epsilon delta : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
    (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S delta) (side : _root_.MIPStarRE.QPBT.PlayerSide) :
    (_root_.MIPStarRE.QPBT.swapUnitary w side)ᴴ * _root_.MIPStarRE.QPBT.swapUnitary w side = 1 := by
  exact mul_eq_one_comm.mp (_root_.MIPStarRE.QPBT.swapUnitary_mul_conjTranspose w side)







end

end MIPStarRE.QPBT

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





/-- At construction error at least one, a universal extraction constant at
least four suffices for the complete witness. This is the large-error branch
at the unchanged nested scale of `exists_extractionWitness_ofGlobalPairWitness`.

**Scope restriction:** Only the region where `deltaConstructPaulis` is at least
one is covered. See the normalization correction in
`docs/paper-gaps/qpbt_extraction-transfer.tex` for blueprint `lem:qld-unitary`,
paper `14_analysis_of_the_pauli_basis_test.tex:1743-1783`.

**Unfaithful:** The proof uses the supplied-witness helper
`exists_extractionWitness_ofGlobalPairWitness_of_four_le`. The global-witness
construction is supplied by `exists_globalPairWitness` in the source-facing
`exists_extractionWitness`; see issue Dengnifer/MIPStarRE-QPBT-bak#123 and
`docs/paper-gaps/qpbt_extraction-transfer.tex`. -/
theorem exists_extractionWitness_ofGlobalPairWitness_of_one_le_construct
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG C : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon) (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG)
    (hC : 4 ≤ C)
    (hconstruct : 1 ≤ _root_.MIPStarRE.QPBT.deltaConstructPaulis C epsilon deltaG P.m P.d P.q) :
    Nonempty (_root_.MIPStarRE.QPBT.ExtractionWitness S w
      (_root_.MIPStarRE.QPBT.deltaExtract C (_root_.MIPStarRE.QPBT.deltaConstructPaulis C epsilon deltaG P.m P.d P.q) P.m P.d P.q)) := by
  apply _root_.MIPStarRE.QPBT.exists_extractionWitness_ofGlobalPairWitness_of_four_le S w
  have hroot := Real.one_le_rpow hconstruct (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hratio : 0 ≤ ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) := by positivity
  unfold _root_.MIPStarRE.QPBT.deltaExtract
  exact hC.trans (le_mul_of_one_le_right (by linarith)
    (hroot.trans (le_add_of_nonneg_right hratio)))









end

end MIPStarRE.QPBT

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



open scoped BigOperators Matrix

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

theorem solution
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (epsilon deltaG : ℝ)
    (hepsilon : 0 ≤ epsilon) (hepsilon_one : epsilon ≤ 1) (hdeltaG : 0 ≤ deltaG)
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon) (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) :
    Nonempty (_root_.MIPStarRE.QPBT.ExtractionWitness S w
      (_root_.MIPStarRE.QPBT.deltaExtract _root_.MIPStarRE.QPBT.pauliBaselineExtractionConstant
        (_root_.MIPStarRE.QPBT.deltaConstructPaulis _root_.MIPStarRE.QPBT.pauliBaselineExtractionConstant
          epsilon deltaG P.m P.d P.q) P.m P.d P.q)) := by
  let C : ℝ := _root_.MIPStarRE.QPBT.pauliBaselineExtractionConstant
  have hCE_C : 2 + 4 * Real.sqrt 172 ≤ C := by
    have hroot := Real.sqrt_nonneg (172 : ℝ)
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 172)
    dsimp [C, _root_.MIPStarRE.QPBT.pauliBaselineExtractionConstant]
    nlinarith
  have hC18 : 18 ≤ C := by
    dsimp [C, _root_.MIPStarRE.QPBT.pauliBaselineExtractionConstant]
    norm_num
  let delta := _root_.MIPStarRE.QPBT.deltaConstructPaulis C epsilon deltaG P.m P.d P.q
  have hmono (K : ℝ) (hK : K ≤ C) :
      _root_.MIPStarRE.QPBT.deltaConstructPaulis K epsilon deltaG P.m P.d P.q ≤ delta :=
    mul_le_mul_of_nonneg_right hK (by positivity)
  have hdelta : 0 ≤ delta := by
    dsimp [delta, C, _root_.MIPStarRE.QPBT.deltaConstructPaulis, _root_.MIPStarRE.QPBT.pauliBaselineExtractionConstant]
    positivity
  by_cases hdelta_one : delta ≤ 1
  · obtain ⟨aux, haux, hclose⟩ :=
      _root_.MIPStarRE.QPBT.exists_extraction_aux_of_global_pair_witness_explicit
        P epsilon deltaG hepsilon hepsilon_one hdeltaG S w
    have hstate_delta :
        ‖S.applyBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) S.psiHat -
          S.idealExpState aux‖ ^ 2 ≤ 16 * delta :=
      hclose
    have hnorm :
        ‖S.applyBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) S.psiHat -
          S.idealExpState aux‖ ≤ 4 * Real.sqrt delta := by
      nlinarith [Real.sq_sqrt hdelta, Real.sqrt_nonneg delta, norm_nonneg
        (S.applyBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) S.psiHat -
          S.idealExpState aux)]
    have habsorb := _root_.MIPStarRE.QPBT.extraction_small_error_absorption C delta P.m P.d P.q
      hC18 hdelta hdelta_one
    refine ⟨{
      swap_right_unitary := _root_.MIPStarRE.QPBT.swapUnitary_mul_conjTranspose w
      swap_left_unitary := _root_.MIPStarRE.QPBT.conjTranspose_mul_swapUnitary w
      aux := aux
      aux_norm := haux
      state_close := hstate_delta.trans habsorb.1
      pauli_close := ?_
    }⟩
    intro side W
    have he := _root_.MIPStarRE.QPBT.evaluated_pauli_tilde_consistency_of_global_pair_witness_explicit
      P epsilon deltaG hepsilon hepsilon_one hdeltaG S w W
    have hdefect : S.evaluatedPauliDefect w side W ≤ delta := by
      cases side
      · exact he.1.trans (hmono _ hCE_C)
      · exact he.2.trans (hmono _ hCE_C)
    apply (S.extraction_pauli_dist_le w aux haux side W).trans
    apply le_trans _ habsorb.2
    push_cast
    linarith
  · exact _root_.MIPStarRE.QPBT.exists_extractionWitness_ofGlobalPairWitness_of_one_le_construct S w
      (by linarith) (le_of_lt (lt_of_not_ge hdelta_one))
