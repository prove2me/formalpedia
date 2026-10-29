-- Prove2me | solution 1 for MIPStarRE.QPBT.dLineDescOf_ldDLineCL
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:55:47.233728+00:00
-- url     : https://prove2.me/submissions/99debeda-3308-4b29-85f6-ac5c76b5d7d6

-- Generated proof for MIPStarRE.QPBT.dLineDescOf_ldDLineCL.
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
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineSupport.lean. -/
/-!
# Generating laws of the restricted line-point distributions

This module rewrites the two restricted line-point laws of
`def:ith-restricted-line` as push-forwards of a single uniformly sampled
low-degree vector conditioned on the coordinate-index fiber of its retained
scalar seed.  In that form the point block, the seed and the direction block
of the sampled vector are visibly the independent generating data of the
restricted law, which is the description used by the sampling procedure of the
sub-line lemma: there the projected pairs are built either from a direction
block inherited from the extended line or from freshly sampled data, and each
is asserted to follow a restricted law.

## References

The generating descriptions support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws themselves are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## The coordinate-index event on a single uniform vector -/







/-! ## Canonical representatives are unchanged by the conditioning maps -/



/-- Two diagonal-line descriptions with the same seed, the same base and the
same direction agree: the stored proofs of `def:line-representative`
invariance and of the prefix-zero condition are propositions and carry no
further data.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem lineDesc_diagonal_congr {L : _root_.MIPStarRE.QPBT.LdParams}
    {b b' d d' : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L} {s : _root_.MIPStarRE.QPBT.ScalarQ L}
    (hb : b = b') (hd : d = d')
    (h1 : _root_.MIPStarRE.QPBT.lineRepMap d b = b)
    (h2 : ∀ j : Fin L.m, j.val < (_root_.MIPStarRE.QPBT.chiIndex L s).val → d j = 0)
    (h1' : _root_.MIPStarRE.QPBT.lineRepMap d' b' = b')
    (h2' : ∀ j : Fin L.m, j.val < (_root_.MIPStarRE.QPBT.chiIndex L s).val → d' j = 0) :
    _root_.MIPStarRE.QPBT.LineDesc.diagonal b s d h1 h2 = _root_.MIPStarRE.QPBT.LineDesc.diagonal b' s d' h1' h2' := by
  subst hb
  subst hd
  rfl





/-! ## Generating laws of the restricted line-point distributions -/





end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/LowDegreeGame.lean. -/
/-!
# The low-degree game

The low-degree component of the Pauli basis test has finite question and answer
alphabets.  Its question maps act explicitly on the point, coordinate, and
direction registers of the ambient coefficient space and have recursive
conditionally linear representations of levels one, two, and three.

## References

The source-facing nodes are blueprint `def:ld-game`,
`def:ld-question-distribution`, and `def:ld-win-predicate`; their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
The exact decomposition of a scalar seed into its coordinate index and its
residue records the balance assertion for the map `chi` in the same source
definition.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section























/-! ### Formalization-only coordinate-index fibers

The following decomposition supplies the equal-fiber calculation used in the
uniform coordinate-index law.
-/



















/-- Zeroing the coordinates preceding a fixed index is idempotent.  This is a
formalization-only consequence of the prefix restriction in
`def:ld-question-distribution`, recorded as `lem:prefix-projection-idempotent`
in blueprint chapter 13. -/
theorem prefixProjection_idempotent {P : _root_.MIPStarRE.QPBT.LdParams} (i : Fin P.m)
    (v : Fin P.m → _root_.MIPStarRE.QPBT.ScalarQ P) :
    _root_.MIPStarRE.QPBT.prefixProjection i (_root_.MIPStarRE.QPBT.prefixProjection i v) = _root_.MIPStarRE.QPBT.prefixProjection i v := by
  funext j
  by_cases h : j.val < i.val
  · simp only [_root_.MIPStarRE.QPBT.prefixProjection, if_pos h]
  · simp only [_root_.MIPStarRE.QPBT.prefixProjection, if_neg h]









































































end

end MIPStarRE.QPBT

/-!
# Generating laws of the restricted line-point distributions

This module rewrites the two restricted line-point laws of
`def:ith-restricted-line` as push-forwards of a single uniformly sampled
low-degree vector conditioned on the coordinate-index fiber of its retained
scalar seed.  In that form the point block, the seed and the direction block
of the sampled vector are visibly the independent generating data of the
restricted law, which is the description used by the sampling procedure of the
sub-line lemma: there the projected pairs are built either from a direction
block inherited from the extended line or from freshly sampled data, and each
is asserted to follow a restricted law.

## References

The generating descriptions support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws themselves are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



/-! ## The coordinate-index event on a single uniform vector -/







/-! ## Canonical representatives are unchanged by the conditioning maps -/

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams) (z : _root_.MIPStarRE.QPBT.LdSpace L) :
    _root_.MIPStarRE.QPBT.dLineDescOf L (_root_.MIPStarRE.QPBT.ldDLineCL L z) = _root_.MIPStarRE.QPBT.dLineDescOf L z := by
  have hdir : _root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex L (_root_.MIPStarRE.QPBT.LdSpace.seed (_root_.MIPStarRE.QPBT.ldDLineCL L z)))
        (_root_.MIPStarRE.QPBT.LdSpace.direction (_root_.MIPStarRE.QPBT.ldDLineCL L z))
      = _root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex L (_root_.MIPStarRE.QPBT.LdSpace.seed z)) (_root_.MIPStarRE.QPBT.LdSpace.direction z) :=
    _root_.MIPStarRE.QPBT.prefixProjection_idempotent _ _
  have hpt : _root_.MIPStarRE.QPBT.lineRepMap
        (_root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex L (_root_.MIPStarRE.QPBT.LdSpace.seed (_root_.MIPStarRE.QPBT.ldDLineCL L z)))
          (_root_.MIPStarRE.QPBT.LdSpace.direction (_root_.MIPStarRE.QPBT.ldDLineCL L z)))
        (_root_.MIPStarRE.QPBT.LdSpace.point (_root_.MIPStarRE.QPBT.ldDLineCL L z))
      = _root_.MIPStarRE.QPBT.lineRepMap
        (_root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex L (_root_.MIPStarRE.QPBT.LdSpace.seed z)) (_root_.MIPStarRE.QPBT.LdSpace.direction z))
        (_root_.MIPStarRE.QPBT.LdSpace.point z) := by
    rw [hdir]
    exact _root_.MIPStarRE.QPBT.lineRepMap_apply_self _ _
  exact _root_.MIPStarRE.QPBT.lineDesc_diagonal_congr hpt hdir _ _ _ _
