-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.exists_opposite_bipartition
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:51:53.662997+00:00
-- url     : https://prove2.me/submissions/b24ee712-55e5-4792-a7ad-1dba022fdc52

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.exists_opposite_bipartition.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Combining_Lines_Construction
import Definitions.Def_QPBT_QPBT_Combining_Points_Orthonormalization
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedPlacement
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

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

/- Source helpers from QPBT/Combining/Points/Orthonormalization.lean. -/
/-!
# Orthonormalization of the sandwich POVM

For each fixed point pair `(x, z)`, the sandwich POVM `R^{x,z}` on one
register placement is consistent with the sandwich POVM on the opposite
placement, with the consistency defect bounded by
`ProjectiveSetting.sandwichDefectBound`.  The orthonormalization lemma
`lem:ortho`, in its explicit-constant form
`projective_rounding_with_explicit_constant`, therefore produces a projective
measurement `Q^{x,z}` on the original local space, within `220 · c^{1/4}` of
`R^{x,z}` on the expanded state, where `c` is that bound.  Choosing such a
measurement for every pair and averaging, the concavity of `t ↦ t^{1/4}`
turns the average of the fiberwise errors into the same function of the
average defect.

The orthonormalization lemma is stated for a bipartite state whose first
tensor factor carries the POVM to be rounded.  The two bipartitions used are
`AA' | BA''(B'B'')`, for Alice's measurements, and `BA'' | AA'(B'B'')`, for
Bob's; the second is introduced here.

## Main results

* `baAaBipartition` with its two placement lemmas.
* `avgOver_rpow_quarter_le`: Jensen's inequality for the fourth root.
* `ProjectiveSetting.exists_projective_close_sandwich`: the fiberwise
  orthonormalization, for any bipartition exhibiting the two placements as
  the two tensor factors.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:786-790`
(the application of the orthonormalization lemma), blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:870-878` (`lem:qld-4-10`), and
`blueprint/src/chapter/ch14_qpbt_observables.tex:395-464` (`lem:ortho`); the
route is explained in `docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## Jensen's inequality for the fourth root -/





/-! ## The bipartition with Bob's registers first -/



namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-- Under the `BA'' | AA'(B'B'')` bipartition, a `BA''` placement is the
ordinary left tensor placement. -/
theorem reindexOp_baAaBipartition_left (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (O : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace _root_.MIPStarRE.QPBT.Placement.BA''.side)) :
    _root_.MIPStarRE.QPBT.reindexOp (_root_.MIPStarRE.QPBT.baAaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (_root_.MIPStarRE.QPBT.heteroKron O
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op ((S.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P) ×
            (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P)))) =
      S.place .BA'' O := by
  ext i j
  obtain ⟨⟨a, a', a''⟩, b, b', b''⟩ := i
  obtain ⟨⟨c, c', c''⟩, d, d', d''⟩ := j
  simp only [_root_.MIPStarRE.QPBT.reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, _root_.MIPStarRE.QPBT.ProjectiveSetting.place, _root_.MIPStarRE.QPBT.baAaBipartition, Equiv.coe_fn_mk, _root_.MIPStarRE.QPBT.heteroKron,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs
  all_goals simp_all
  all_goals rfl

/-- Under the `BA'' | AA'(B'B'')` bipartition, an `AA'` placement is the
ordinary right tensor placement, with identity on the unused EPR pair. -/
theorem reindexOp_baAaBipartition_right (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (O : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace _root_.MIPStarRE.QPBT.Placement.AA'.side)) :
    _root_.MIPStarRE.QPBT.reindexOp (_root_.MIPStarRE.QPBT.baAaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P))
          (_root_.MIPStarRE.QPBT.heteroKron O (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P)))) =
      S.place .AA' O := by
  ext i j
  obtain ⟨⟨a, a', a''⟩, b, b', b''⟩ := i
  obtain ⟨⟨c, c', c''⟩, d, d', d''⟩ := j
  simp only [_root_.MIPStarRE.QPBT.reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, _root_.MIPStarRE.QPBT.ProjectiveSetting.place, _root_.MIPStarRE.QPBT.baAaBipartition, Equiv.coe_fn_mk, _root_.MIPStarRE.QPBT.heteroKron,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs
  all_goals simp_all
  all_goals rfl

/-! ## Transport along a bipartition -/







end ProjectiveSetting

end

end MIPStarRE.QPBT

/-!
# Construction of consistent combined lines

The heterogeneous pasting theorem bounds the actual X-Z-X measurement.
Polynomial absorption produces a line error for each polynomial point family.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The source and completed-answer distinctions remain
as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400 in

theorem solution {params : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {error : ℝ} (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error)
    (first second : _root_.MIPStarRE.QPBT.Placement) (hopposite : first.IsOpposite second) :
    ∃ equivalence : _root_.MIPStarRE.QPBT.SixReg params setting.toStrategy.ιA setting.toStrategy.ιB ≃
        setting.ExpandedLocalSpace first.side ×
          (setting.ExpandedLocalSpace second.side ×
            (_root_.MIPStarRE.QPBT.PauliRegister params × _root_.MIPStarRE.QPBT.PauliRegister params)),
      (∀ operator : _root_.LIDT.MIPStarRE.Quantum.Op (setting.ExpandedLocalSpace first.side),
        _root_.MIPStarRE.QPBT.reindexOp equivalence (_root_.MIPStarRE.QPBT.heteroKron operator 1) = setting.place first operator) ∧
      (∀ operator : _root_.LIDT.MIPStarRE.Quantum.Op (setting.ExpandedLocalSpace second.side),
        _root_.MIPStarRE.QPBT.reindexOp equivalence (_root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.heteroKron operator
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister params × _root_.MIPStarRE.QPBT.PauliRegister params)))) =
          setting.place second operator) := by
  classical
  cases first <;> cases second <;> try exact False.elim hopposite
  · exact ⟨_root_.MIPStarRE.QPBT.ProjectiveSetting.aaBaBipartition params _ _, setting.reindexOp_aaBaBipartition_left,
      setting.reindexOp_aaBaBipartition_right⟩
  · exact ⟨_root_.MIPStarRE.QPBT.baAaBipartition params _ _, setting.reindexOp_baAaBipartition_left,
      setting.reindexOp_baAaBipartition_right⟩
  · refine ⟨_root_.MIPStarRE.QPBT.bbAbBipartition params _ _, ?_, ?_⟩
    · intro operator
      ext row column
      change operator (row.2.1, row.2.2.1) (column.2.1, column.2.2.1) *
        (1 : _root_.LIDT.MIPStarRE.Quantum.Op ((setting.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister params) ×
          (_root_.MIPStarRE.QPBT.PauliRegister params × _root_.MIPStarRE.QPBT.PauliRegister params)))
          ((row.1.1, row.2.2.2), row.1.2) ((column.1.1, column.2.2.2), column.1.2) = _
      simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff]
      split_ifs <;> simp_all
    · intro operator
      ext row column
      change (1 : _root_.LIDT.MIPStarRE.Quantum.Op (setting.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister params))
        (row.2.1, row.2.2.1) (column.2.1, column.2.2.1) *
          (operator (row.1.1, row.2.2.2) (column.1.1, column.2.2.2) *
            (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister params × _root_.MIPStarRE.QPBT.PauliRegister params)) row.1.2 column.1.2) = _
      simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff]
      split_ifs <;> simp_all
  · exact ⟨_root_.MIPStarRE.QPBT.ProjectiveSetting.abBbBipartition params _ _, setting.reindexOp_abBbBipartition_left,
      setting.reindexOp_abBbBipartition_right⟩
